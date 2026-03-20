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
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
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
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
uint8_t l_Lean_Environment_isProjectionFn(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_registerSimpAttr(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpExtension_getTheorems___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Simp_neutralConfig;
lean_object* l_Lean_Meta_Simp_mkContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEST(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
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
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinDSimproc(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__52___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "paramLet"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__52___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__52___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__52___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_WF_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__52___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__52___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12__value_aux_0),((lean_object*)&l_Lean_Elab_WF_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__52___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__52___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12__value_aux_1),((lean_object*)&l_Lean_Elab_WF_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(24, 25, 43, 203, 194, 237, 195, 214)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__52___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__52___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12__value_aux_2),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__52___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12__value),LEAN_SCALAR_PTR_LITERAL(158, 69, 53, 139, 5, 90, 17, 138)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__52___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__52___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__52_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__52_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12____boxed(lean_object*);
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
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Elab_WF_preprocess_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_WF_preprocess_spec__5___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_WF_preprocess_spec__5___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Elab_WF_preprocess_spec__5___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_WF_preprocess_spec__5___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_WF_preprocess_spec__5___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_WF_preprocess_spec__5___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_WF_preprocess_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_WF_preprocess_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_WF_preprocess_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_WF_preprocess_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__7___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__7(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preprocess___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preprocess___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__10_spec__12___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__10_spec__12___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__6___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__6___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__6___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__6___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__6___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__6___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_preprocess_spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_preprocess_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_WF_preprocess___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_preprocess___lam__0___closed__0;
static lean_once_cell_t l_Lean_Elab_WF_preprocess___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_preprocess___lam__0___closed__1;
static lean_once_cell_t l_Lean_Elab_WF_preprocess___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_preprocess___lam__0___closed__2;
static lean_once_cell_t l_Lean_Elab_WF_preprocess___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_preprocess___lam__0___closed__3;
static lean_once_cell_t l_Lean_Elab_WF_preprocess___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_preprocess___lam__0___closed__4;
static lean_once_cell_t l_Lean_Elab_WF_preprocess___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_preprocess___lam__0___closed__5;
static lean_once_cell_t l_Lean_Elab_WF_preprocess___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_preprocess___lam__0___closed__6;
static lean_once_cell_t l_Lean_Elab_WF_preprocess___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_preprocess___lam__0___closed__7;
static lean_once_cell_t l_Lean_Elab_WF_preprocess___lam__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_preprocess___lam__0___closed__8;
static lean_once_cell_t l_Lean_Elab_WF_preprocess___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_preprocess___lam__0___closed__9;
static const lean_string_object l_Lean_Elab_WF_preprocess___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l_Lean_Elab_WF_preprocess___lam__0___closed__10 = (const lean_object*)&l_Lean_Elab_WF_preprocess___lam__0___closed__10_value;
static const lean_ctor_object l_Lean_Elab_WF_preprocess___lam__0___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_WF_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l_Lean_Elab_WF_preprocess___lam__0___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_WF_preprocess___lam__0___closed__11_value_aux_0),((lean_object*)&l_Lean_Elab_WF_preprocess___lam__0___closed__10_value),LEAN_SCALAR_PTR_LITERAL(127, 238, 145, 63, 173, 125, 183, 95)}};
static const lean_ctor_object l_Lean_Elab_WF_preprocess___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_WF_preprocess___lam__0___closed__11_value_aux_1),((lean_object*)&l_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(235, 76, 232, 241, 91, 21, 77, 227)}};
static const lean_object* l_Lean_Elab_WF_preprocess___lam__0___closed__11 = (const lean_object*)&l_Lean_Elab_WF_preprocess___lam__0___closed__11_value;
static const lean_string_object l_Lean_Elab_WF_preprocess___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Attach-introduction:"};
static const lean_object* l_Lean_Elab_WF_preprocess___lam__0___closed__12 = (const lean_object*)&l_Lean_Elab_WF_preprocess___lam__0___closed__12_value;
static lean_once_cell_t l_Lean_Elab_WF_preprocess___lam__0___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_preprocess___lam__0___closed__13;
static const lean_string_object l_Lean_Elab_WF_preprocess___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "\nto"};
static const lean_object* l_Lean_Elab_WF_preprocess___lam__0___closed__14 = (const lean_object*)&l_Lean_Elab_WF_preprocess___lam__0___closed__14_value;
static lean_once_cell_t l_Lean_Elab_WF_preprocess___lam__0___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_preprocess___lam__0___closed__15;
static const lean_string_object l_Lean_Elab_WF_preprocess___lam__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "\ncleand up to "};
static const lean_object* l_Lean_Elab_WF_preprocess___lam__0___closed__16 = (const lean_object*)&l_Lean_Elab_WF_preprocess___lam__0___closed__16_value;
static lean_once_cell_t l_Lean_Elab_WF_preprocess___lam__0___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_preprocess___lam__0___closed__17;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preprocess___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preprocess___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_WF_preprocess___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_WF_preprocess___lam__1___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_WF_preprocess___closed__0 = (const lean_object*)&l_Lean_Elab_WF_preprocess___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preprocess___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__10_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__10_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_inc(v_name_1_);
v___x_12_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_12_, 0, v_name_1_);
lean_ctor_set(v___x_12_, 1, v_ref_3_);
lean_ctor_set(v___x_12_, 2, v___x_10_);
lean_ctor_set(v___x_12_, 3, v_descr_6_);
lean_inc(v_name_1_);
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
lean_object* v_a_94_; lean_object* v___x_95_; lean_object* v_maxSteps_96_; lean_object* v_maxDischargeDepth_97_; uint8_t v_contextual_98_; uint8_t v_memoize_99_; uint8_t v_singlePass_100_; uint8_t v_zeta_101_; uint8_t v_beta_102_; uint8_t v_eta_103_; uint8_t v_etaStruct_104_; uint8_t v_iota_105_; uint8_t v_proj_106_; uint8_t v_decide_107_; uint8_t v_arith_108_; uint8_t v_autoUnfold_109_; uint8_t v_failIfUnchanged_110_; uint8_t v_ground_111_; uint8_t v_unfoldPartialApp_112_; uint8_t v_zetaDelta_113_; uint8_t v_index_114_; uint8_t v_implicitDefEqProofs_115_; uint8_t v_zetaUnused_116_; uint8_t v_catchRuntime_117_; uint8_t v_zetaHave_118_; uint8_t v_letToHave_119_; uint8_t v_bitVecOfNat_120_; uint8_t v_warnExponents_121_; uint8_t v_suggestions_122_; lean_object* v_maxSuggestions_123_; uint8_t v_locals_124_; uint8_t v_instances_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_139_; 
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
v_isSharedCheck_139_ = !lean_is_exclusive(v___x_95_);
if (v_isSharedCheck_139_ == 0)
{
v___x_127_ = v___x_95_;
v_isShared_128_ = v_isSharedCheck_139_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_maxSuggestions_123_);
lean_inc(v_maxDischargeDepth_97_);
lean_inc(v_maxSteps_96_);
lean_dec(v___x_95_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_139_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
uint8_t v___x_129_; uint8_t v___x_130_; lean_object* v___x_132_; 
v___x_129_ = 1;
v___x_130_ = 0;
if (v_isShared_128_ == 0)
{
v___x_132_ = v___x_127_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v_maxSteps_96_);
lean_ctor_set(v_reuseFailAlloc_138_, 1, v_maxDischargeDepth_97_);
lean_ctor_set(v_reuseFailAlloc_138_, 2, v_maxSuggestions_123_);
lean_ctor_set_uint8(v_reuseFailAlloc_138_, sizeof(void*)*3, v_contextual_98_);
lean_ctor_set_uint8(v_reuseFailAlloc_138_, sizeof(void*)*3 + 1, v_memoize_99_);
lean_ctor_set_uint8(v_reuseFailAlloc_138_, sizeof(void*)*3 + 2, v_singlePass_100_);
lean_ctor_set_uint8(v_reuseFailAlloc_138_, sizeof(void*)*3 + 3, v_zeta_101_);
lean_ctor_set_uint8(v_reuseFailAlloc_138_, sizeof(void*)*3 + 4, v_beta_102_);
lean_ctor_set_uint8(v_reuseFailAlloc_138_, sizeof(void*)*3 + 5, v_eta_103_);
lean_ctor_set_uint8(v_reuseFailAlloc_138_, sizeof(void*)*3 + 6, v_etaStruct_104_);
lean_ctor_set_uint8(v_reuseFailAlloc_138_, sizeof(void*)*3 + 7, v_iota_105_);
lean_ctor_set_uint8(v_reuseFailAlloc_138_, sizeof(void*)*3 + 8, v_proj_106_);
lean_ctor_set_uint8(v_reuseFailAlloc_138_, sizeof(void*)*3 + 9, v_decide_107_);
lean_ctor_set_uint8(v_reuseFailAlloc_138_, sizeof(void*)*3 + 10, v_arith_108_);
lean_ctor_set_uint8(v_reuseFailAlloc_138_, sizeof(void*)*3 + 11, v_autoUnfold_109_);
lean_ctor_set_uint8(v_reuseFailAlloc_138_, sizeof(void*)*3 + 13, v_failIfUnchanged_110_);
lean_ctor_set_uint8(v_reuseFailAlloc_138_, sizeof(void*)*3 + 14, v_ground_111_);
lean_ctor_set_uint8(v_reuseFailAlloc_138_, sizeof(void*)*3 + 15, v_unfoldPartialApp_112_);
lean_ctor_set_uint8(v_reuseFailAlloc_138_, sizeof(void*)*3 + 16, v_zetaDelta_113_);
lean_ctor_set_uint8(v_reuseFailAlloc_138_, sizeof(void*)*3 + 17, v_index_114_);
lean_ctor_set_uint8(v_reuseFailAlloc_138_, sizeof(void*)*3 + 18, v_implicitDefEqProofs_115_);
lean_ctor_set_uint8(v_reuseFailAlloc_138_, sizeof(void*)*3 + 19, v_zetaUnused_116_);
lean_ctor_set_uint8(v_reuseFailAlloc_138_, sizeof(void*)*3 + 20, v_catchRuntime_117_);
lean_ctor_set_uint8(v_reuseFailAlloc_138_, sizeof(void*)*3 + 21, v_zetaHave_118_);
lean_ctor_set_uint8(v_reuseFailAlloc_138_, sizeof(void*)*3 + 22, v_letToHave_119_);
lean_ctor_set_uint8(v_reuseFailAlloc_138_, sizeof(void*)*3 + 24, v_bitVecOfNat_120_);
lean_ctor_set_uint8(v_reuseFailAlloc_138_, sizeof(void*)*3 + 25, v_warnExponents_121_);
lean_ctor_set_uint8(v_reuseFailAlloc_138_, sizeof(void*)*3 + 26, v_suggestions_122_);
lean_ctor_set_uint8(v_reuseFailAlloc_138_, sizeof(void*)*3 + 27, v_locals_124_);
lean_ctor_set_uint8(v_reuseFailAlloc_138_, sizeof(void*)*3 + 28, v_instances_125_);
v___x_132_ = v_reuseFailAlloc_138_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
lean_ctor_set_uint8(v___x_132_, sizeof(void*)*3 + 12, v___x_129_);
lean_ctor_set_uint8(v___x_132_, sizeof(void*)*3 + 23, v___x_130_);
v___x_133_ = lean_unsigned_to_nat(1u);
v___x_134_ = lean_mk_empty_array_with_capacity(v___x_133_);
v___x_135_ = lean_array_push(v___x_134_, v_a_94_);
v___x_136_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__4, &l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__4);
v___x_137_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_132_, v___x_135_, v___x_136_, v_a_88_, v_a_89_, v_a_90_);
return v___x_137_;
}
}
}
else
{
lean_object* v_a_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_147_; 
v_a_140_ = lean_ctor_get(v___x_93_, 0);
v_isSharedCheck_147_ = !lean_is_exclusive(v___x_93_);
if (v_isSharedCheck_147_ == 0)
{
v___x_142_ = v___x_93_;
v_isShared_143_ = v_isSharedCheck_147_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_a_140_);
lean_dec(v___x_93_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_147_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v___x_145_; 
if (v_isShared_143_ == 0)
{
v___x_145_ = v___x_142_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v_a_140_);
v___x_145_ = v_reuseFailAlloc_146_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
return v___x_145_;
}
}
}
}
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext(lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg(v_a_153_, v_a_155_, v_a_156_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___boxed(lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext(v_a_159_, v_a_160_, v_a_161_, v_a_162_);
lean_dec(v_a_162_);
lean_dec_ref(v_a_161_);
lean_dec(v_a_160_);
lean_dec_ref(v_a_159_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_isWfParam_x3f(lean_object* v_e_168_){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; uint8_t v___x_171_; 
v___x_169_ = ((lean_object*)(l_Lean_Elab_WF_isWfParam_x3f___closed__1));
v___x_170_ = lean_unsigned_to_nat(2u);
v___x_171_ = l_Lean_Expr_isAppOfArity(v_e_168_, v___x_169_, v___x_170_);
if (v___x_171_ == 0)
{
lean_object* v___x_172_; 
v___x_172_ = lean_box(0);
return v___x_172_;
}
else
{
lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_173_ = l_Lean_Expr_appArg_x21(v_e_168_);
v___x_174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_174_, 0, v___x_173_);
return v___x_174_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_isWfParam_x3f___boxed(lean_object* v_e_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_Lean_Elab_WF_isWfParam_x3f(v_e_175_);
lean_dec_ref(v_e_175_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkWfParam(lean_object* v_e_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_183_ = ((lean_object*)(l_Lean_Elab_WF_isWfParam_x3f___closed__1));
v___x_184_ = lean_unsigned_to_nat(1u);
v___x_185_ = lean_mk_empty_array_with_capacity(v___x_184_);
v___x_186_ = lean_array_push(v___x_185_, v_e_177_);
v___x_187_ = l_Lean_Meta_mkAppM(v___x_183_, v___x_186_, v_a_178_, v_a_179_, v_a_180_, v_a_181_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkWfParam___boxed(lean_object* v_e_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l_Lean_Elab_WF_mkWfParam(v_e_188_, v_a_189_, v_a_190_, v_a_191_, v_a_192_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___00Lean_Elab_WF_paramProj_spec__0___redArg(lean_object* v_declName_195_, lean_object* v___y_196_){
_start:
{
lean_object* v___x_198_; lean_object* v_env_199_; uint8_t v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_198_ = lean_st_ref_get(v___y_196_);
v_env_199_ = lean_ctor_get(v___x_198_, 0);
lean_inc_ref(v_env_199_);
lean_dec(v___x_198_);
v___x_200_ = l_Lean_Environment_isProjectionFn(v_env_199_, v_declName_195_);
v___x_201_ = lean_box(v___x_200_);
v___x_202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_202_, 0, v___x_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___00Lean_Elab_WF_paramProj_spec__0___redArg___boxed(lean_object* v_declName_203_, lean_object* v___y_204_, lean_object* v___y_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l_Lean_isProjectionFn___at___00Lean_Elab_WF_paramProj_spec__0___redArg(v_declName_203_, v___y_204_);
lean_dec(v___y_204_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___00Lean_Elab_WF_paramProj_spec__0(lean_object* v_declName_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = l_Lean_isProjectionFn___at___00Lean_Elab_WF_paramProj_spec__0___redArg(v_declName_207_, v___y_214_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___00Lean_Elab_WF_paramProj_spec__0___boxed(lean_object* v_declName_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l_Lean_isProjectionFn___at___00Lean_Elab_WF_paramProj_spec__0(v_declName_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_, v___y_224_);
lean_dec(v___y_224_);
lean_dec_ref(v___y_223_);
lean_dec(v___y_222_);
lean_dec_ref(v___y_221_);
lean_dec(v___y_220_);
lean_dec_ref(v___y_219_);
lean_dec(v___y_218_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramProj(lean_object* v_e_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_){
_start:
{
uint8_t v___x_238_; 
v___x_238_ = l_Lean_Expr_isApp(v_e_229_);
if (v___x_238_ == 0)
{
lean_object* v___x_239_; lean_object* v___x_240_; 
lean_dec(v_a_236_);
lean_dec_ref(v_a_235_);
lean_dec(v_a_234_);
lean_dec_ref(v_a_233_);
lean_dec_ref(v_e_229_);
v___x_239_ = ((lean_object*)(l_Lean_Elab_WF_paramProj___closed__0));
v___x_240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_240_, 0, v___x_239_);
return v___x_240_;
}
else
{
lean_object* v_fn_241_; lean_object* v_arg_242_; lean_object* v___x_243_; 
v_fn_241_ = lean_ctor_get(v_e_229_, 0);
lean_inc_ref(v_fn_241_);
v_arg_242_ = lean_ctor_get(v_e_229_, 1);
v___x_243_ = l_Lean_Elab_WF_isWfParam_x3f(v_arg_242_);
if (lean_obj_tag(v___x_243_) == 1)
{
lean_object* v_val_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_287_; 
v_val_244_ = lean_ctor_get(v___x_243_, 0);
v_isSharedCheck_287_ = !lean_is_exclusive(v___x_243_);
if (v_isSharedCheck_287_ == 0)
{
v___x_246_ = v___x_243_;
v_isShared_247_ = v_isSharedCheck_287_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_val_244_);
lean_dec(v___x_243_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_287_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v_f_248_; uint8_t v___x_249_; 
v_f_248_ = l_Lean_Expr_getAppFn(v_e_229_);
lean_dec_ref(v_e_229_);
v___x_249_ = l_Lean_Expr_isConst(v_f_248_);
if (v___x_249_ == 0)
{
lean_object* v___x_250_; lean_object* v___x_252_; 
lean_dec_ref(v_f_248_);
lean_dec(v_val_244_);
lean_dec_ref(v_fn_241_);
lean_dec(v_a_236_);
lean_dec_ref(v_a_235_);
lean_dec(v_a_234_);
lean_dec_ref(v_a_233_);
v___x_250_ = ((lean_object*)(l_Lean_Elab_WF_paramProj___closed__0));
if (v_isShared_247_ == 0)
{
lean_ctor_set_tag(v___x_246_, 0);
lean_ctor_set(v___x_246_, 0, v___x_250_);
v___x_252_ = v___x_246_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v___x_250_);
v___x_252_ = v_reuseFailAlloc_253_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
return v___x_252_;
}
}
else
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v_a_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_286_; 
v___x_254_ = l_Lean_Expr_constName_x21(v_f_248_);
lean_dec_ref(v_f_248_);
v___x_255_ = l_Lean_isProjectionFn___at___00Lean_Elab_WF_paramProj_spec__0___redArg(v___x_254_, v_a_236_);
v_a_256_ = lean_ctor_get(v___x_255_, 0);
v_isSharedCheck_286_ = !lean_is_exclusive(v___x_255_);
if (v_isSharedCheck_286_ == 0)
{
v___x_258_ = v___x_255_;
v_isShared_259_ = v_isSharedCheck_286_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_a_256_);
lean_dec(v___x_255_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_286_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
uint8_t v___x_260_; 
v___x_260_ = lean_unbox(v_a_256_);
lean_dec(v_a_256_);
if (v___x_260_ == 0)
{
lean_object* v___x_261_; lean_object* v___x_263_; 
lean_del_object(v___x_246_);
lean_dec(v_val_244_);
lean_dec_ref(v_fn_241_);
lean_dec(v_a_236_);
lean_dec_ref(v_a_235_);
lean_dec(v_a_234_);
lean_dec_ref(v_a_233_);
v___x_261_ = ((lean_object*)(l_Lean_Elab_WF_paramProj___closed__0));
if (v_isShared_259_ == 0)
{
lean_ctor_set(v___x_258_, 0, v___x_261_);
v___x_263_ = v___x_258_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v___x_261_);
v___x_263_ = v_reuseFailAlloc_264_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
return v___x_263_;
}
}
else
{
lean_object* v___x_265_; lean_object* v___x_266_; 
lean_del_object(v___x_258_);
v___x_265_ = l_Lean_Expr_app___override(v_fn_241_, v_val_244_);
v___x_266_ = l_Lean_Elab_WF_mkWfParam(v___x_265_, v_a_233_, v_a_234_, v_a_235_, v_a_236_);
if (lean_obj_tag(v___x_266_) == 0)
{
lean_object* v_a_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_277_; 
v_a_267_ = lean_ctor_get(v___x_266_, 0);
v_isSharedCheck_277_ = !lean_is_exclusive(v___x_266_);
if (v_isSharedCheck_277_ == 0)
{
v___x_269_ = v___x_266_;
v_isShared_270_ = v_isSharedCheck_277_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_a_267_);
lean_dec(v___x_266_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_277_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v___x_272_; 
if (v_isShared_247_ == 0)
{
lean_ctor_set_tag(v___x_246_, 0);
lean_ctor_set(v___x_246_, 0, v_a_267_);
v___x_272_ = v___x_246_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v_a_267_);
v___x_272_ = v_reuseFailAlloc_276_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
lean_object* v___x_274_; 
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 0, v___x_272_);
v___x_274_ = v___x_269_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v___x_272_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
}
}
else
{
lean_object* v_a_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_285_; 
lean_del_object(v___x_246_);
v_a_278_ = lean_ctor_get(v___x_266_, 0);
v_isSharedCheck_285_ = !lean_is_exclusive(v___x_266_);
if (v_isSharedCheck_285_ == 0)
{
v___x_280_ = v___x_266_;
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_a_278_);
lean_dec(v___x_266_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_283_; 
if (v_isShared_281_ == 0)
{
v___x_283_ = v___x_280_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v_a_278_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
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
lean_object* v___x_288_; lean_object* v___x_289_; 
lean_dec(v___x_243_);
lean_dec_ref(v_fn_241_);
lean_dec(v_a_236_);
lean_dec_ref(v_a_235_);
lean_dec(v_a_234_);
lean_dec_ref(v_a_233_);
lean_dec_ref(v_e_229_);
v___x_288_ = ((lean_object*)(l_Lean_Elab_WF_paramProj___closed__0));
v___x_289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
return v___x_289_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramProj___boxed(lean_object* v_e_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l_Lean_Elab_WF_paramProj(v_e_290_, v_a_291_, v_a_292_, v_a_293_, v_a_294_, v_a_295_, v_a_296_, v_a_297_);
lean_dec(v_a_293_);
lean_dec_ref(v_a_292_);
lean_dec(v_a_291_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__26_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_12_(){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_311_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__26___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_12_));
v___x_312_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__26___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_12_));
v___x_313_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_paramProj___boxed), 9, 0);
v___x_314_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_311_, v___x_312_, v___x_313_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__26_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_12____boxed(lean_object* v_a_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__26_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_12_();
return v_res_316_;
}
}
static lean_object* _init_l_Lean_Elab_WF_paramProj___regBuiltin_Lean_Elab_WF_paramProj_declare__1___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_14_(void){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_317_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_paramProj___boxed), 9, 0);
v___x_318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_318_, 0, v___x_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramProj___regBuiltin_Lean_Elab_WF_paramProj_declare__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_14_(){
_start:
{
lean_object* v___x_320_; uint8_t v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_320_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__26___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_12_));
v___x_321_ = 1;
v___x_322_ = lean_obj_once(&l_Lean_Elab_WF_paramProj___regBuiltin_Lean_Elab_WF_paramProj_declare__1___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_14_, &l_Lean_Elab_WF_paramProj___regBuiltin_Lean_Elab_WF_paramProj_declare__1___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_14__once, _init_l_Lean_Elab_WF_paramProj___regBuiltin_Lean_Elab_WF_paramProj_declare__1___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_14_);
v___x_323_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_320_, v___x_321_, v___x_322_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramProj___regBuiltin_Lean_Elab_WF_paramProj_declare__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_14____boxed(lean_object* v_a_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l_Lean_Elab_WF_paramProj___regBuiltin_Lean_Elab_WF_paramProj_declare__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_14_();
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1___redArg___lam__0(lean_object* v_k_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v_b_330_, lean_object* v_c_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_){
_start:
{
lean_object* v___x_337_; 
v___x_337_ = lean_apply_10(v_k_326_, v_b_330_, v_c_331_, v___y_327_, v___y_328_, v___y_329_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, lean_box(0));
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1___redArg___lam__0___boxed(lean_object* v_k_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v_b_342_, lean_object* v_c_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1___redArg___lam__0(v_k_338_, v___y_339_, v___y_340_, v___y_341_, v_b_342_, v_c_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1___redArg(lean_object* v_e_350_, lean_object* v_k_351_, uint8_t v_cleanupAnnotations_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_){
_start:
{
lean_object* v___f_361_; uint8_t v___x_362_; uint8_t v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
v___f_361_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1___redArg___lam__0___boxed), 11, 4);
lean_closure_set(v___f_361_, 0, v_k_351_);
lean_closure_set(v___f_361_, 1, v___y_353_);
lean_closure_set(v___f_361_, 2, v___y_354_);
lean_closure_set(v___f_361_, 3, v___y_355_);
v___x_362_ = 1;
v___x_363_ = 0;
v___x_364_ = lean_box(0);
v___x_365_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_350_, v___x_362_, v___x_363_, v___x_362_, v___x_363_, v___x_364_, v___f_361_, v_cleanupAnnotations_352_, v___y_356_, v___y_357_, v___y_358_, v___y_359_);
if (lean_obj_tag(v___x_365_) == 0)
{
return v___x_365_;
}
else
{
lean_object* v_a_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_373_; 
v_a_366_ = lean_ctor_get(v___x_365_, 0);
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_365_);
if (v_isSharedCheck_373_ == 0)
{
v___x_368_ = v___x_365_;
v_isShared_369_ = v_isSharedCheck_373_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_a_366_);
lean_dec(v___x_365_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_373_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_371_; 
if (v_isShared_369_ == 0)
{
v___x_371_ = v___x_368_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_a_366_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1___redArg___boxed(lean_object* v_e_374_, lean_object* v_k_375_, lean_object* v_cleanupAnnotations_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_385_; lean_object* v_res_386_; 
v_cleanupAnnotations_boxed_385_ = lean_unbox(v_cleanupAnnotations_376_);
v_res_386_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1___redArg(v_e_374_, v_k_375_, v_cleanupAnnotations_boxed_385_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1(lean_object* v_00_u03b1_387_, lean_object* v_e_388_, lean_object* v_k_389_, uint8_t v_cleanupAnnotations_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_){
_start:
{
lean_object* v___x_399_; 
v___x_399_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1___redArg(v_e_388_, v_k_389_, v_cleanupAnnotations_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1___boxed(lean_object* v_00_u03b1_400_, lean_object* v_e_401_, lean_object* v_k_402_, lean_object* v_cleanupAnnotations_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_412_; lean_object* v_res_413_; 
v_cleanupAnnotations_boxed_412_ = lean_unbox(v_cleanupAnnotations_403_);
v_res_413_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1(v_00_u03b1_400_, v_e_401_, v_k_402_, v_cleanupAnnotations_boxed_412_, v___y_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__0___redArg(size_t v_sz_414_, size_t v_i_415_, lean_object* v_bs_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_){
_start:
{
uint8_t v___x_422_; 
v___x_422_ = lean_usize_dec_lt(v_i_415_, v_sz_414_);
if (v___x_422_ == 0)
{
lean_object* v___x_423_; 
lean_dec(v___y_420_);
lean_dec_ref(v___y_419_);
lean_dec(v___y_418_);
lean_dec_ref(v___y_417_);
v___x_423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_423_, 0, v_bs_416_);
return v___x_423_;
}
else
{
lean_object* v_v_424_; lean_object* v___x_425_; 
v_v_424_ = lean_array_uget_borrowed(v_bs_416_, v_i_415_);
lean_inc(v___y_420_);
lean_inc_ref(v___y_419_);
lean_inc(v___y_418_);
lean_inc_ref(v___y_417_);
lean_inc(v_v_424_);
v___x_425_ = l_Lean_Elab_WF_mkWfParam(v_v_424_, v___y_417_, v___y_418_, v___y_419_, v___y_420_);
if (lean_obj_tag(v___x_425_) == 0)
{
lean_object* v_a_426_; lean_object* v___x_427_; lean_object* v_bs_x27_428_; size_t v___x_429_; size_t v___x_430_; lean_object* v___x_431_; 
v_a_426_ = lean_ctor_get(v___x_425_, 0);
lean_inc(v_a_426_);
lean_dec_ref(v___x_425_);
v___x_427_ = lean_unsigned_to_nat(0u);
v_bs_x27_428_ = lean_array_uset(v_bs_416_, v_i_415_, v___x_427_);
v___x_429_ = ((size_t)1ULL);
v___x_430_ = lean_usize_add(v_i_415_, v___x_429_);
v___x_431_ = lean_array_uset(v_bs_x27_428_, v_i_415_, v_a_426_);
v_i_415_ = v___x_430_;
v_bs_416_ = v___x_431_;
goto _start;
}
else
{
lean_object* v_a_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_440_; 
lean_dec(v___y_420_);
lean_dec_ref(v___y_419_);
lean_dec(v___y_418_);
lean_dec_ref(v___y_417_);
lean_dec_ref(v_bs_416_);
v_a_433_ = lean_ctor_get(v___x_425_, 0);
v_isSharedCheck_440_ = !lean_is_exclusive(v___x_425_);
if (v_isSharedCheck_440_ == 0)
{
v___x_435_ = v___x_425_;
v_isShared_436_ = v_isSharedCheck_440_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_a_433_);
lean_dec(v___x_425_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_440_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v___x_438_; 
if (v_isShared_436_ == 0)
{
v___x_438_ = v___x_435_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v_a_433_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__0___redArg___boxed(lean_object* v_sz_441_, lean_object* v_i_442_, lean_object* v_bs_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_){
_start:
{
size_t v_sz_boxed_449_; size_t v_i_boxed_450_; lean_object* v_res_451_; 
v_sz_boxed_449_ = lean_unbox_usize(v_sz_441_);
lean_dec(v_sz_441_);
v_i_boxed_450_ = lean_unbox_usize(v_i_442_);
lean_dec(v_i_442_);
v_res_451_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__0___redArg(v_sz_boxed_449_, v_i_boxed_450_, v_bs_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__4___lam__0(uint8_t v___x_452_, lean_object* v_xs_453_, lean_object* v_body_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_){
_start:
{
size_t v_sz_463_; size_t v___x_464_; lean_object* v___x_465_; 
v_sz_463_ = lean_array_size(v_xs_453_);
v___x_464_ = ((size_t)0ULL);
lean_inc(v___y_461_);
lean_inc_ref(v___y_460_);
lean_inc(v___y_459_);
lean_inc_ref(v___y_458_);
lean_inc_ref(v_xs_453_);
v___x_465_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__0___redArg(v_sz_463_, v___x_464_, v_xs_453_, v___y_458_, v___y_459_, v___y_460_, v___y_461_);
if (lean_obj_tag(v___x_465_) == 0)
{
lean_object* v_a_466_; lean_object* v___x_467_; uint8_t v___x_468_; uint8_t v___x_469_; lean_object* v___x_470_; 
v_a_466_ = lean_ctor_get(v___x_465_, 0);
lean_inc(v_a_466_);
lean_dec_ref(v___x_465_);
v___x_467_ = l_Lean_Expr_replaceFVars(v_body_454_, v_xs_453_, v_a_466_);
lean_dec(v_a_466_);
v___x_468_ = 0;
v___x_469_ = 1;
v___x_470_ = l_Lean_Meta_mkLambdaFVars(v_xs_453_, v___x_467_, v___x_468_, v___x_452_, v___x_468_, v___x_452_, v___x_469_, v___y_458_, v___y_459_, v___y_460_, v___y_461_);
lean_dec(v___y_461_);
lean_dec_ref(v___y_460_);
lean_dec(v___y_459_);
lean_dec_ref(v___y_458_);
lean_dec_ref(v_xs_453_);
return v___x_470_;
}
else
{
lean_object* v_a_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_478_; 
lean_dec(v___y_461_);
lean_dec_ref(v___y_460_);
lean_dec(v___y_459_);
lean_dec_ref(v___y_458_);
lean_dec_ref(v_xs_453_);
v_a_471_ = lean_ctor_get(v___x_465_, 0);
v_isSharedCheck_478_ = !lean_is_exclusive(v___x_465_);
if (v_isSharedCheck_478_ == 0)
{
v___x_473_ = v___x_465_;
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_a_471_);
lean_dec(v___x_465_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_476_; 
if (v_isShared_474_ == 0)
{
v___x_476_ = v___x_473_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v_a_471_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__4___lam__0___boxed(lean_object* v___x_479_, lean_object* v_xs_480_, lean_object* v_body_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_){
_start:
{
uint8_t v___x_22200__boxed_490_; lean_object* v_res_491_; 
v___x_22200__boxed_490_ = lean_unbox(v___x_479_);
v_res_491_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__4___lam__0(v___x_22200__boxed_490_, v_xs_480_, v_body_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_);
lean_dec(v___y_484_);
lean_dec_ref(v___y_483_);
lean_dec(v___y_482_);
lean_dec_ref(v_body_481_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__4(size_t v_sz_492_, size_t v_i_493_, lean_object* v_bs_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_){
_start:
{
uint8_t v___x_503_; 
v___x_503_ = lean_usize_dec_lt(v_i_493_, v_sz_492_);
if (v___x_503_ == 0)
{
lean_object* v___x_504_; 
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
lean_dec(v___y_499_);
lean_dec_ref(v___y_498_);
lean_dec(v___y_497_);
lean_dec_ref(v___y_496_);
lean_dec(v___y_495_);
v___x_504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_504_, 0, v_bs_494_);
return v___x_504_;
}
else
{
lean_object* v___x_505_; lean_object* v___f_506_; lean_object* v_v_507_; uint8_t v___x_508_; lean_object* v___x_509_; 
v___x_505_ = lean_box(v___x_503_);
v___f_506_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__4___lam__0___boxed), 11, 1);
lean_closure_set(v___f_506_, 0, v___x_505_);
v_v_507_ = lean_array_uget_borrowed(v_bs_494_, v_i_493_);
v___x_508_ = 0;
lean_inc(v___y_501_);
lean_inc_ref(v___y_500_);
lean_inc(v___y_499_);
lean_inc_ref(v___y_498_);
lean_inc(v___y_497_);
lean_inc_ref(v___y_496_);
lean_inc(v___y_495_);
lean_inc(v_v_507_);
v___x_509_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1___redArg(v_v_507_, v___f_506_, v___x_508_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_);
if (lean_obj_tag(v___x_509_) == 0)
{
lean_object* v_a_510_; lean_object* v___x_511_; lean_object* v_bs_x27_512_; size_t v___x_513_; size_t v___x_514_; lean_object* v___x_515_; 
v_a_510_ = lean_ctor_get(v___x_509_, 0);
lean_inc(v_a_510_);
lean_dec_ref(v___x_509_);
v___x_511_ = lean_unsigned_to_nat(0u);
v_bs_x27_512_ = lean_array_uset(v_bs_494_, v_i_493_, v___x_511_);
v___x_513_ = ((size_t)1ULL);
v___x_514_ = lean_usize_add(v_i_493_, v___x_513_);
v___x_515_ = lean_array_uset(v_bs_x27_512_, v_i_493_, v_a_510_);
v_i_493_ = v___x_514_;
v_bs_494_ = v___x_515_;
goto _start;
}
else
{
lean_object* v_a_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_524_; 
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
lean_dec(v___y_499_);
lean_dec_ref(v___y_498_);
lean_dec(v___y_497_);
lean_dec_ref(v___y_496_);
lean_dec(v___y_495_);
lean_dec_ref(v_bs_494_);
v_a_517_ = lean_ctor_get(v___x_509_, 0);
v_isSharedCheck_524_ = !lean_is_exclusive(v___x_509_);
if (v_isSharedCheck_524_ == 0)
{
v___x_519_ = v___x_509_;
v_isShared_520_ = v_isSharedCheck_524_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_a_517_);
lean_dec(v___x_509_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_524_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v___x_522_; 
if (v_isShared_520_ == 0)
{
v___x_522_ = v___x_519_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v_a_517_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__4___boxed(lean_object* v_sz_525_, lean_object* v_i_526_, lean_object* v_bs_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_){
_start:
{
size_t v_sz_boxed_536_; size_t v_i_boxed_537_; lean_object* v_res_538_; 
v_sz_boxed_536_ = lean_unbox_usize(v_sz_525_);
lean_dec(v_sz_525_);
v_i_boxed_537_ = lean_unbox_usize(v_i_526_);
lean_dec(v_i_526_);
v_res_538_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__4(v_sz_boxed_536_, v_i_boxed_537_, v_bs_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15_spec__16(lean_object* v_msgData_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_){
_start:
{
lean_object* v___x_545_; lean_object* v_env_546_; lean_object* v___x_547_; lean_object* v_mctx_548_; lean_object* v_lctx_549_; lean_object* v_options_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_545_ = lean_st_ref_get(v___y_543_);
v_env_546_ = lean_ctor_get(v___x_545_, 0);
lean_inc_ref(v_env_546_);
lean_dec(v___x_545_);
v___x_547_ = lean_st_ref_get(v___y_541_);
v_mctx_548_ = lean_ctor_get(v___x_547_, 0);
lean_inc_ref(v_mctx_548_);
lean_dec(v___x_547_);
v_lctx_549_ = lean_ctor_get(v___y_540_, 2);
v_options_550_ = lean_ctor_get(v___y_542_, 2);
lean_inc_ref(v_options_550_);
lean_inc_ref(v_lctx_549_);
v___x_551_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_551_, 0, v_env_546_);
lean_ctor_set(v___x_551_, 1, v_mctx_548_);
lean_ctor_set(v___x_551_, 2, v_lctx_549_);
lean_ctor_set(v___x_551_, 3, v_options_550_);
v___x_552_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_552_, 0, v___x_551_);
lean_ctor_set(v___x_552_, 1, v_msgData_539_);
v___x_553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_553_, 0, v___x_552_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15_spec__16___boxed(lean_object* v_msgData_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15_spec__16(v_msgData_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
lean_dec(v___y_556_);
lean_dec_ref(v___y_555_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15___redArg(lean_object* v_msg_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_){
_start:
{
lean_object* v_ref_567_; lean_object* v___x_568_; lean_object* v_a_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_577_; 
v_ref_567_ = lean_ctor_get(v___y_564_, 5);
v___x_568_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15_spec__16(v_msg_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_);
v_a_569_ = lean_ctor_get(v___x_568_, 0);
v_isSharedCheck_577_ = !lean_is_exclusive(v___x_568_);
if (v_isSharedCheck_577_ == 0)
{
v___x_571_ = v___x_568_;
v_isShared_572_ = v_isSharedCheck_577_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_a_569_);
lean_dec(v___x_568_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_577_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v___x_573_; lean_object* v___x_575_; 
lean_inc(v_ref_567_);
v___x_573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_573_, 0, v_ref_567_);
lean_ctor_set(v___x_573_, 1, v_a_569_);
if (v_isShared_572_ == 0)
{
lean_ctor_set_tag(v___x_571_, 1);
lean_ctor_set(v___x_571_, 0, v___x_573_);
v___x_575_ = v___x_571_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v___x_573_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
return v___x_575_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15___redArg___boxed(lean_object* v_msg_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15___redArg(v_msg_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_);
lean_dec(v___y_582_);
lean_dec_ref(v___y_581_);
lean_dec(v___y_580_);
lean_dec_ref(v___y_579_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13___redArg(lean_object* v_ref_585_, lean_object* v_msg_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_){
_start:
{
lean_object* v_fileName_595_; lean_object* v_fileMap_596_; lean_object* v_options_597_; lean_object* v_currRecDepth_598_; lean_object* v_maxRecDepth_599_; lean_object* v_ref_600_; lean_object* v_currNamespace_601_; lean_object* v_openDecls_602_; lean_object* v_initHeartbeats_603_; lean_object* v_maxHeartbeats_604_; lean_object* v_quotContext_605_; lean_object* v_currMacroScope_606_; uint8_t v_diag_607_; lean_object* v_cancelTk_x3f_608_; uint8_t v_suppressElabErrors_609_; lean_object* v_inheritedTraceOptions_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_619_; 
v_fileName_595_ = lean_ctor_get(v___y_592_, 0);
v_fileMap_596_ = lean_ctor_get(v___y_592_, 1);
v_options_597_ = lean_ctor_get(v___y_592_, 2);
v_currRecDepth_598_ = lean_ctor_get(v___y_592_, 3);
v_maxRecDepth_599_ = lean_ctor_get(v___y_592_, 4);
v_ref_600_ = lean_ctor_get(v___y_592_, 5);
v_currNamespace_601_ = lean_ctor_get(v___y_592_, 6);
v_openDecls_602_ = lean_ctor_get(v___y_592_, 7);
v_initHeartbeats_603_ = lean_ctor_get(v___y_592_, 8);
v_maxHeartbeats_604_ = lean_ctor_get(v___y_592_, 9);
v_quotContext_605_ = lean_ctor_get(v___y_592_, 10);
v_currMacroScope_606_ = lean_ctor_get(v___y_592_, 11);
v_diag_607_ = lean_ctor_get_uint8(v___y_592_, sizeof(void*)*14);
v_cancelTk_x3f_608_ = lean_ctor_get(v___y_592_, 12);
v_suppressElabErrors_609_ = lean_ctor_get_uint8(v___y_592_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_610_ = lean_ctor_get(v___y_592_, 13);
v_isSharedCheck_619_ = !lean_is_exclusive(v___y_592_);
if (v_isSharedCheck_619_ == 0)
{
v___x_612_ = v___y_592_;
v_isShared_613_ = v_isSharedCheck_619_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_inheritedTraceOptions_610_);
lean_inc(v_cancelTk_x3f_608_);
lean_inc(v_currMacroScope_606_);
lean_inc(v_quotContext_605_);
lean_inc(v_maxHeartbeats_604_);
lean_inc(v_initHeartbeats_603_);
lean_inc(v_openDecls_602_);
lean_inc(v_currNamespace_601_);
lean_inc(v_ref_600_);
lean_inc(v_maxRecDepth_599_);
lean_inc(v_currRecDepth_598_);
lean_inc(v_options_597_);
lean_inc(v_fileMap_596_);
lean_inc(v_fileName_595_);
lean_dec(v___y_592_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_619_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v_ref_614_; lean_object* v___x_616_; 
v_ref_614_ = l_Lean_replaceRef(v_ref_585_, v_ref_600_);
lean_dec(v_ref_600_);
if (v_isShared_613_ == 0)
{
lean_ctor_set(v___x_612_, 5, v_ref_614_);
v___x_616_ = v___x_612_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v_fileName_595_);
lean_ctor_set(v_reuseFailAlloc_618_, 1, v_fileMap_596_);
lean_ctor_set(v_reuseFailAlloc_618_, 2, v_options_597_);
lean_ctor_set(v_reuseFailAlloc_618_, 3, v_currRecDepth_598_);
lean_ctor_set(v_reuseFailAlloc_618_, 4, v_maxRecDepth_599_);
lean_ctor_set(v_reuseFailAlloc_618_, 5, v_ref_614_);
lean_ctor_set(v_reuseFailAlloc_618_, 6, v_currNamespace_601_);
lean_ctor_set(v_reuseFailAlloc_618_, 7, v_openDecls_602_);
lean_ctor_set(v_reuseFailAlloc_618_, 8, v_initHeartbeats_603_);
lean_ctor_set(v_reuseFailAlloc_618_, 9, v_maxHeartbeats_604_);
lean_ctor_set(v_reuseFailAlloc_618_, 10, v_quotContext_605_);
lean_ctor_set(v_reuseFailAlloc_618_, 11, v_currMacroScope_606_);
lean_ctor_set(v_reuseFailAlloc_618_, 12, v_cancelTk_x3f_608_);
lean_ctor_set(v_reuseFailAlloc_618_, 13, v_inheritedTraceOptions_610_);
lean_ctor_set_uint8(v_reuseFailAlloc_618_, sizeof(void*)*14, v_diag_607_);
lean_ctor_set_uint8(v_reuseFailAlloc_618_, sizeof(void*)*14 + 1, v_suppressElabErrors_609_);
v___x_616_ = v_reuseFailAlloc_618_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
lean_object* v___x_617_; 
v___x_617_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15___redArg(v_msg_586_, v___y_590_, v___y_591_, v___x_616_, v___y_593_);
lean_dec_ref(v___x_616_);
return v___x_617_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13___redArg___boxed(lean_object* v_ref_620_, lean_object* v_msg_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_){
_start:
{
lean_object* v_res_630_; 
v_res_630_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13___redArg(v_ref_620_, v_msg_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_);
lean_dec(v___y_628_);
lean_dec(v___y_626_);
lean_dec_ref(v___y_625_);
lean_dec(v___y_624_);
lean_dec_ref(v___y_623_);
lean_dec(v___y_622_);
lean_dec(v_ref_620_);
return v_res_630_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__0(void){
_start:
{
lean_object* v___x_631_; 
v___x_631_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_631_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__1(void){
_start:
{
lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_632_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__0);
v___x_633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_633_, 0, v___x_632_);
return v___x_633_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__2(void){
_start:
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_634_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_635_ = lean_unsigned_to_nat(0u);
v___x_636_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_636_, 0, v___x_635_);
lean_ctor_set(v___x_636_, 1, v___x_635_);
lean_ctor_set(v___x_636_, 2, v___x_635_);
lean_ctor_set(v___x_636_, 3, v___x_634_);
lean_ctor_set(v___x_636_, 4, v___x_634_);
lean_ctor_set(v___x_636_, 5, v___x_634_);
lean_ctor_set(v___x_636_, 6, v___x_634_);
lean_ctor_set(v___x_636_, 7, v___x_634_);
lean_ctor_set(v___x_636_, 8, v___x_634_);
return v___x_636_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__3(void){
_start:
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_637_ = lean_unsigned_to_nat(32u);
v___x_638_ = lean_mk_empty_array_with_capacity(v___x_637_);
v___x_639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_639_, 0, v___x_638_);
return v___x_639_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__4(void){
_start:
{
size_t v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_640_ = ((size_t)5ULL);
v___x_641_ = lean_unsigned_to_nat(0u);
v___x_642_ = lean_unsigned_to_nat(32u);
v___x_643_ = lean_mk_empty_array_with_capacity(v___x_642_);
v___x_644_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__3);
v___x_645_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_645_, 0, v___x_644_);
lean_ctor_set(v___x_645_, 1, v___x_643_);
lean_ctor_set(v___x_645_, 2, v___x_641_);
lean_ctor_set(v___x_645_, 3, v___x_641_);
lean_ctor_set_usize(v___x_645_, 4, v___x_640_);
return v___x_645_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__5(void){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_646_ = lean_box(1);
v___x_647_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__4);
v___x_648_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_649_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_649_, 0, v___x_648_);
lean_ctor_set(v___x_649_, 1, v___x_647_);
lean_ctor_set(v___x_649_, 2, v___x_646_);
return v___x_649_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__7(void){
_start:
{
lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_651_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__6));
v___x_652_ = l_Lean_stringToMessageData(v___x_651_);
return v___x_652_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__9(void){
_start:
{
lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_654_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__8));
v___x_655_ = l_Lean_stringToMessageData(v___x_654_);
return v___x_655_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__11(void){
_start:
{
lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_657_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__10));
v___x_658_ = l_Lean_stringToMessageData(v___x_657_);
return v___x_658_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__13(void){
_start:
{
lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_660_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__12));
v___x_661_ = l_Lean_stringToMessageData(v___x_660_);
return v___x_661_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__15(void){
_start:
{
lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_663_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__14));
v___x_664_ = l_Lean_stringToMessageData(v___x_663_);
return v___x_664_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__17(void){
_start:
{
lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_666_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__16));
v___x_667_ = l_Lean_stringToMessageData(v___x_666_);
return v___x_667_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__19(void){
_start:
{
lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_669_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__18));
v___x_670_ = l_Lean_stringToMessageData(v___x_669_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg(lean_object* v_msg_671_, lean_object* v_declHint_672_, lean_object* v___y_673_){
_start:
{
lean_object* v___x_675_; lean_object* v_env_676_; uint8_t v___x_677_; 
v___x_675_ = lean_st_ref_get(v___y_673_);
v_env_676_ = lean_ctor_get(v___x_675_, 0);
lean_inc_ref(v_env_676_);
lean_dec(v___x_675_);
v___x_677_ = l_Lean_Name_isAnonymous(v_declHint_672_);
if (v___x_677_ == 0)
{
uint8_t v_isExporting_678_; 
v_isExporting_678_ = lean_ctor_get_uint8(v_env_676_, sizeof(void*)*8);
if (v_isExporting_678_ == 0)
{
lean_object* v___x_679_; 
lean_dec_ref(v_env_676_);
lean_dec(v_declHint_672_);
v___x_679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_679_, 0, v_msg_671_);
return v___x_679_;
}
else
{
lean_object* v___x_680_; uint8_t v___x_681_; 
lean_inc_ref(v_env_676_);
v___x_680_ = l_Lean_Environment_setExporting(v_env_676_, v___x_677_);
lean_inc(v_declHint_672_);
lean_inc_ref(v___x_680_);
v___x_681_ = l_Lean_Environment_contains(v___x_680_, v_declHint_672_, v_isExporting_678_);
if (v___x_681_ == 0)
{
lean_object* v___x_682_; 
lean_dec_ref(v___x_680_);
lean_dec_ref(v_env_676_);
lean_dec(v_declHint_672_);
v___x_682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_682_, 0, v_msg_671_);
return v___x_682_;
}
else
{
lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v_c_688_; lean_object* v___x_689_; 
v___x_683_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__2);
v___x_684_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__5);
v___x_685_ = l_Lean_Options_empty;
v___x_686_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_686_, 0, v___x_680_);
lean_ctor_set(v___x_686_, 1, v___x_683_);
lean_ctor_set(v___x_686_, 2, v___x_684_);
lean_ctor_set(v___x_686_, 3, v___x_685_);
lean_inc(v_declHint_672_);
v___x_687_ = l_Lean_MessageData_ofConstName(v_declHint_672_, v___x_677_);
v_c_688_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_688_, 0, v___x_686_);
lean_ctor_set(v_c_688_, 1, v___x_687_);
v___x_689_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_676_, v_declHint_672_);
if (lean_obj_tag(v___x_689_) == 0)
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
lean_dec_ref(v_env_676_);
lean_dec(v_declHint_672_);
v___x_690_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__7);
v___x_691_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_691_, 0, v___x_690_);
lean_ctor_set(v___x_691_, 1, v_c_688_);
v___x_692_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__9);
v___x_693_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_693_, 0, v___x_691_);
lean_ctor_set(v___x_693_, 1, v___x_692_);
v___x_694_ = l_Lean_MessageData_note(v___x_693_);
v___x_695_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_695_, 0, v_msg_671_);
lean_ctor_set(v___x_695_, 1, v___x_694_);
v___x_696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_696_, 0, v___x_695_);
return v___x_696_;
}
else
{
lean_object* v_val_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_732_; 
v_val_697_ = lean_ctor_get(v___x_689_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_732_ == 0)
{
v___x_699_ = v___x_689_;
v_isShared_700_ = v_isSharedCheck_732_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_val_697_);
lean_dec(v___x_689_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_732_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v_mod_704_; uint8_t v___x_705_; 
v___x_701_ = lean_box(0);
v___x_702_ = l_Lean_Environment_header(v_env_676_);
lean_dec_ref(v_env_676_);
v___x_703_ = l_Lean_EnvironmentHeader_moduleNames(v___x_702_);
v_mod_704_ = lean_array_get(v___x_701_, v___x_703_, v_val_697_);
lean_dec(v_val_697_);
lean_dec_ref(v___x_703_);
v___x_705_ = l_Lean_isPrivateName(v_declHint_672_);
lean_dec(v_declHint_672_);
if (v___x_705_ == 0)
{
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_717_; 
v___x_706_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__11);
v___x_707_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_707_, 0, v___x_706_);
lean_ctor_set(v___x_707_, 1, v_c_688_);
v___x_708_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__13);
v___x_709_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_709_, 0, v___x_707_);
lean_ctor_set(v___x_709_, 1, v___x_708_);
v___x_710_ = l_Lean_MessageData_ofName(v_mod_704_);
v___x_711_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_711_, 0, v___x_709_);
lean_ctor_set(v___x_711_, 1, v___x_710_);
v___x_712_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__15);
v___x_713_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_713_, 0, v___x_711_);
lean_ctor_set(v___x_713_, 1, v___x_712_);
v___x_714_ = l_Lean_MessageData_note(v___x_713_);
v___x_715_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_715_, 0, v_msg_671_);
lean_ctor_set(v___x_715_, 1, v___x_714_);
if (v_isShared_700_ == 0)
{
lean_ctor_set_tag(v___x_699_, 0);
lean_ctor_set(v___x_699_, 0, v___x_715_);
v___x_717_ = v___x_699_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v___x_715_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
else
{
lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_730_; 
v___x_719_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__7);
v___x_720_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_720_, 0, v___x_719_);
lean_ctor_set(v___x_720_, 1, v_c_688_);
v___x_721_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__17);
v___x_722_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_722_, 0, v___x_720_);
lean_ctor_set(v___x_722_, 1, v___x_721_);
v___x_723_ = l_Lean_MessageData_ofName(v_mod_704_);
v___x_724_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_724_, 0, v___x_722_);
lean_ctor_set(v___x_724_, 1, v___x_723_);
v___x_725_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__19);
v___x_726_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_726_, 0, v___x_724_);
lean_ctor_set(v___x_726_, 1, v___x_725_);
v___x_727_ = l_Lean_MessageData_note(v___x_726_);
v___x_728_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_728_, 0, v_msg_671_);
lean_ctor_set(v___x_728_, 1, v___x_727_);
if (v_isShared_700_ == 0)
{
lean_ctor_set_tag(v___x_699_, 0);
lean_ctor_set(v___x_699_, 0, v___x_728_);
v___x_730_ = v___x_699_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v___x_728_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_733_; 
lean_dec_ref(v_env_676_);
lean_dec(v_declHint_672_);
v___x_733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_733_, 0, v_msg_671_);
return v___x_733_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___boxed(lean_object* v_msg_734_, lean_object* v_declHint_735_, lean_object* v___y_736_, lean_object* v___y_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg(v_msg_734_, v_declHint_735_, v___y_736_);
lean_dec(v___y_736_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12(lean_object* v_msg_739_, lean_object* v_declHint_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_){
_start:
{
lean_object* v___x_749_; lean_object* v_a_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_759_; 
v___x_749_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg(v_msg_739_, v_declHint_740_, v___y_747_);
v_a_750_ = lean_ctor_get(v___x_749_, 0);
v_isSharedCheck_759_ = !lean_is_exclusive(v___x_749_);
if (v_isSharedCheck_759_ == 0)
{
v___x_752_ = v___x_749_;
v_isShared_753_ = v_isSharedCheck_759_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_a_750_);
lean_dec(v___x_749_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_759_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_757_; 
v___x_754_ = l_Lean_unknownIdentifierMessageTag;
v___x_755_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_755_, 0, v___x_754_);
lean_ctor_set(v___x_755_, 1, v_a_750_);
if (v_isShared_753_ == 0)
{
lean_ctor_set(v___x_752_, 0, v___x_755_);
v___x_757_ = v___x_752_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v___x_755_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
return v___x_757_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12___boxed(lean_object* v_msg_760_, lean_object* v_declHint_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12(v_msg_760_, v_declHint_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_);
lean_dec(v___y_768_);
lean_dec_ref(v___y_767_);
lean_dec(v___y_766_);
lean_dec_ref(v___y_765_);
lean_dec(v___y_764_);
lean_dec_ref(v___y_763_);
lean_dec(v___y_762_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11___redArg(lean_object* v_ref_771_, lean_object* v_msg_772_, lean_object* v_declHint_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_){
_start:
{
lean_object* v___x_782_; lean_object* v_a_783_; lean_object* v___x_784_; 
v___x_782_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12(v_msg_772_, v_declHint_773_, v___y_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_);
v_a_783_ = lean_ctor_get(v___x_782_, 0);
lean_inc(v_a_783_);
lean_dec_ref(v___x_782_);
v___x_784_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13___redArg(v_ref_771_, v_a_783_, v___y_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_);
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11___redArg___boxed(lean_object* v_ref_785_, lean_object* v_msg_786_, lean_object* v_declHint_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_){
_start:
{
lean_object* v_res_796_; 
v_res_796_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11___redArg(v_ref_785_, v_msg_786_, v_declHint_787_, v___y_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_);
lean_dec(v___y_794_);
lean_dec(v___y_792_);
lean_dec_ref(v___y_791_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
lean_dec(v___y_788_);
lean_dec(v_ref_785_);
return v_res_796_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_798_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__0));
v___x_799_ = l_Lean_stringToMessageData(v___x_798_);
return v___x_799_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_801_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__2));
v___x_802_ = l_Lean_stringToMessageData(v___x_801_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg(lean_object* v_ref_803_, lean_object* v_constName_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_){
_start:
{
lean_object* v___x_813_; uint8_t v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_813_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__1);
v___x_814_ = 0;
lean_inc(v_constName_804_);
v___x_815_ = l_Lean_MessageData_ofConstName(v_constName_804_, v___x_814_);
v___x_816_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_816_, 0, v___x_813_);
lean_ctor_set(v___x_816_, 1, v___x_815_);
v___x_817_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__3);
v___x_818_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_818_, 0, v___x_816_);
lean_ctor_set(v___x_818_, 1, v___x_817_);
v___x_819_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11___redArg(v_ref_803_, v___x_818_, v_constName_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___boxed(lean_object* v_ref_820_, lean_object* v_constName_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg(v_ref_820_, v_constName_821_, v___y_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_);
lean_dec(v___y_828_);
lean_dec(v___y_826_);
lean_dec_ref(v___y_825_);
lean_dec(v___y_824_);
lean_dec_ref(v___y_823_);
lean_dec(v___y_822_);
lean_dec(v_ref_820_);
return v_res_830_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3___redArg(lean_object* v_constName_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_){
_start:
{
lean_object* v_ref_840_; lean_object* v___x_841_; 
v_ref_840_ = lean_ctor_get(v___y_837_, 5);
lean_inc(v_ref_840_);
v___x_841_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg(v_ref_840_, v_constName_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_);
lean_dec(v_ref_840_);
return v___x_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3___redArg___boxed(lean_object* v_constName_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3___redArg(v_constName_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_);
lean_dec(v___y_849_);
lean_dec(v___y_847_);
lean_dec_ref(v___y_846_);
lean_dec(v___y_845_);
lean_dec_ref(v___y_844_);
lean_dec(v___y_843_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2(lean_object* v_constName_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_){
_start:
{
lean_object* v___x_861_; lean_object* v_env_862_; uint8_t v___x_863_; lean_object* v___x_864_; 
v___x_861_ = lean_st_ref_get(v___y_859_);
v_env_862_ = lean_ctor_get(v___x_861_, 0);
lean_inc_ref(v_env_862_);
lean_dec(v___x_861_);
v___x_863_ = 0;
lean_inc(v_constName_852_);
v___x_864_ = l_Lean_Environment_find_x3f(v_env_862_, v_constName_852_, v___x_863_);
if (lean_obj_tag(v___x_864_) == 0)
{
lean_object* v___x_865_; 
v___x_865_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3___redArg(v_constName_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_);
return v___x_865_;
}
else
{
lean_object* v_val_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_873_; 
lean_dec_ref(v___y_858_);
lean_dec(v_constName_852_);
v_val_866_ = lean_ctor_get(v___x_864_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_873_ == 0)
{
v___x_868_ = v___x_864_;
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_val_866_);
lean_dec(v___x_864_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_871_; 
if (v_isShared_869_ == 0)
{
lean_ctor_set_tag(v___x_868_, 0);
v___x_871_ = v___x_868_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_val_866_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2___boxed(lean_object* v_constName_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2(v_constName_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_);
lean_dec(v___y_881_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec(v___y_877_);
lean_dec_ref(v___y_876_);
lean_dec(v___y_875_);
return v_res_883_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___closed__0(void){
_start:
{
lean_object* v___x_884_; 
v___x_884_ = l_instMonadEST(lean_box(0), lean_box(0));
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3(lean_object* v_msg_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_){
_start:
{
lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v_toApplicative_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_964_; 
v___x_898_ = lean_obj_once(&l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___closed__0, &l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___closed__0_once, _init_l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___closed__0);
v___x_899_ = l_ReaderT_instMonad___redArg(v___x_898_);
v_toApplicative_900_ = lean_ctor_get(v___x_899_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v___x_899_);
if (v_isSharedCheck_964_ == 0)
{
lean_object* v_unused_965_; 
v_unused_965_ = lean_ctor_get(v___x_899_, 1);
lean_dec(v_unused_965_);
v___x_902_ = v___x_899_;
v_isShared_903_ = v_isSharedCheck_964_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_toApplicative_900_);
lean_dec(v___x_899_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_964_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v_toFunctor_904_; lean_object* v_toSeq_905_; lean_object* v_toSeqLeft_906_; lean_object* v_toSeqRight_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_962_; 
v_toFunctor_904_ = lean_ctor_get(v_toApplicative_900_, 0);
v_toSeq_905_ = lean_ctor_get(v_toApplicative_900_, 2);
v_toSeqLeft_906_ = lean_ctor_get(v_toApplicative_900_, 3);
v_toSeqRight_907_ = lean_ctor_get(v_toApplicative_900_, 4);
v_isSharedCheck_962_ = !lean_is_exclusive(v_toApplicative_900_);
if (v_isSharedCheck_962_ == 0)
{
lean_object* v_unused_963_; 
v_unused_963_ = lean_ctor_get(v_toApplicative_900_, 1);
lean_dec(v_unused_963_);
v___x_909_ = v_toApplicative_900_;
v_isShared_910_ = v_isSharedCheck_962_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_toSeqRight_907_);
lean_inc(v_toSeqLeft_906_);
lean_inc(v_toSeq_905_);
lean_inc(v_toFunctor_904_);
lean_dec(v_toApplicative_900_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_962_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___f_911_; lean_object* v___f_912_; lean_object* v___f_913_; lean_object* v___f_914_; lean_object* v___x_915_; lean_object* v___f_916_; lean_object* v___f_917_; lean_object* v___f_918_; lean_object* v___x_920_; 
v___f_911_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___closed__1));
v___f_912_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___closed__2));
lean_inc_ref(v_toFunctor_904_);
v___f_913_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_913_, 0, v_toFunctor_904_);
v___f_914_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_914_, 0, v_toFunctor_904_);
v___x_915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_915_, 0, v___f_913_);
lean_ctor_set(v___x_915_, 1, v___f_914_);
v___f_916_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_916_, 0, v_toSeqRight_907_);
v___f_917_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_917_, 0, v_toSeqLeft_906_);
v___f_918_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_918_, 0, v_toSeq_905_);
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 4, v___f_916_);
lean_ctor_set(v___x_909_, 3, v___f_917_);
lean_ctor_set(v___x_909_, 2, v___f_918_);
lean_ctor_set(v___x_909_, 1, v___f_911_);
lean_ctor_set(v___x_909_, 0, v___x_915_);
v___x_920_ = v___x_909_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v___x_915_);
lean_ctor_set(v_reuseFailAlloc_961_, 1, v___f_911_);
lean_ctor_set(v_reuseFailAlloc_961_, 2, v___f_918_);
lean_ctor_set(v_reuseFailAlloc_961_, 3, v___f_917_);
lean_ctor_set(v_reuseFailAlloc_961_, 4, v___f_916_);
v___x_920_ = v_reuseFailAlloc_961_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
lean_object* v___x_922_; 
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 1, v___f_912_);
lean_ctor_set(v___x_902_, 0, v___x_920_);
v___x_922_ = v___x_902_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v___x_920_);
lean_ctor_set(v_reuseFailAlloc_960_, 1, v___f_912_);
v___x_922_ = v_reuseFailAlloc_960_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
lean_object* v___x_923_; lean_object* v_toApplicative_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_958_; 
v___x_923_ = l_ReaderT_instMonad___redArg(v___x_922_);
v_toApplicative_924_ = lean_ctor_get(v___x_923_, 0);
v_isSharedCheck_958_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_958_ == 0)
{
lean_object* v_unused_959_; 
v_unused_959_ = lean_ctor_get(v___x_923_, 1);
lean_dec(v_unused_959_);
v___x_926_ = v___x_923_;
v_isShared_927_ = v_isSharedCheck_958_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_toApplicative_924_);
lean_dec(v___x_923_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_958_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v_toFunctor_928_; lean_object* v_toSeq_929_; lean_object* v_toSeqLeft_930_; lean_object* v_toSeqRight_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_956_; 
v_toFunctor_928_ = lean_ctor_get(v_toApplicative_924_, 0);
v_toSeq_929_ = lean_ctor_get(v_toApplicative_924_, 2);
v_toSeqLeft_930_ = lean_ctor_get(v_toApplicative_924_, 3);
v_toSeqRight_931_ = lean_ctor_get(v_toApplicative_924_, 4);
v_isSharedCheck_956_ = !lean_is_exclusive(v_toApplicative_924_);
if (v_isSharedCheck_956_ == 0)
{
lean_object* v_unused_957_; 
v_unused_957_ = lean_ctor_get(v_toApplicative_924_, 1);
lean_dec(v_unused_957_);
v___x_933_ = v_toApplicative_924_;
v_isShared_934_ = v_isSharedCheck_956_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_toSeqRight_931_);
lean_inc(v_toSeqLeft_930_);
lean_inc(v_toSeq_929_);
lean_inc(v_toFunctor_928_);
lean_dec(v_toApplicative_924_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_956_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___f_935_; lean_object* v___f_936_; lean_object* v___f_937_; lean_object* v___f_938_; lean_object* v___x_939_; lean_object* v___f_940_; lean_object* v___f_941_; lean_object* v___f_942_; lean_object* v___x_944_; 
v___f_935_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___closed__3));
v___f_936_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___closed__4));
lean_inc_ref(v_toFunctor_928_);
v___f_937_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_937_, 0, v_toFunctor_928_);
v___f_938_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_938_, 0, v_toFunctor_928_);
v___x_939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_939_, 0, v___f_937_);
lean_ctor_set(v___x_939_, 1, v___f_938_);
v___f_940_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_940_, 0, v_toSeqRight_931_);
v___f_941_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_941_, 0, v_toSeqLeft_930_);
v___f_942_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_942_, 0, v_toSeq_929_);
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 4, v___f_940_);
lean_ctor_set(v___x_933_, 3, v___f_941_);
lean_ctor_set(v___x_933_, 2, v___f_942_);
lean_ctor_set(v___x_933_, 1, v___f_935_);
lean_ctor_set(v___x_933_, 0, v___x_939_);
v___x_944_ = v___x_933_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v___x_939_);
lean_ctor_set(v_reuseFailAlloc_955_, 1, v___f_935_);
lean_ctor_set(v_reuseFailAlloc_955_, 2, v___f_942_);
lean_ctor_set(v_reuseFailAlloc_955_, 3, v___f_941_);
lean_ctor_set(v_reuseFailAlloc_955_, 4, v___f_940_);
v___x_944_ = v_reuseFailAlloc_955_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
lean_object* v___x_946_; 
if (v_isShared_927_ == 0)
{
lean_ctor_set(v___x_926_, 1, v___f_936_);
lean_ctor_set(v___x_926_, 0, v___x_944_);
v___x_946_ = v___x_926_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v___x_944_);
lean_ctor_set(v_reuseFailAlloc_954_, 1, v___f_936_);
v___x_946_ = v_reuseFailAlloc_954_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_14106__overap_952_; lean_object* v___x_953_; 
v___x_947_ = l_ReaderT_instMonad___redArg(v___x_946_);
v___x_948_ = l_ReaderT_instMonad___redArg(v___x_947_);
v___x_949_ = l_ReaderT_instMonad___redArg(v___x_948_);
v___x_950_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_951_ = l_instInhabitedOfMonad___redArg(v___x_949_, v___x_950_);
v___x_14106__overap_952_ = lean_panic_fn(v___x_951_, v_msg_889_);
v___x_953_ = lean_apply_8(v___x_14106__overap_952_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, lean_box(0));
return v___x_953_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___boxed(lean_object* v_msg_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3(v_msg_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
return v_res_975_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5___closed__3(void){
_start:
{
lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_979_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5___closed__2));
v___x_980_ = lean_unsigned_to_nat(53u);
v___x_981_ = lean_unsigned_to_nat(62u);
v___x_982_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5___closed__1));
v___x_983_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5___closed__0));
v___x_984_ = l_mkPanicMessageWithDecl(v___x_983_, v___x_982_, v___x_981_, v___x_980_, v___x_979_);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5(size_t v_sz_985_, size_t v_i_986_, lean_object* v_bs_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_){
_start:
{
uint8_t v___x_996_; 
v___x_996_ = lean_usize_dec_lt(v_i_986_, v_sz_985_);
if (v___x_996_ == 0)
{
lean_object* v___x_997_; 
lean_dec(v___y_994_);
lean_dec_ref(v___y_993_);
lean_dec(v___y_992_);
lean_dec_ref(v___y_991_);
lean_dec(v___y_990_);
lean_dec_ref(v___y_989_);
lean_dec(v___y_988_);
v___x_997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_997_, 0, v_bs_987_);
return v___x_997_;
}
else
{
lean_object* v_v_998_; lean_object* v___x_999_; 
v_v_998_ = lean_array_uget_borrowed(v_bs_987_, v_i_986_);
lean_inc_ref(v___y_993_);
lean_inc(v_v_998_);
v___x_999_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2(v_v_998_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_object* v_a_1000_; lean_object* v___x_1001_; lean_object* v_bs_x27_1002_; lean_object* v_a_1004_; 
v_a_1000_ = lean_ctor_get(v___x_999_, 0);
lean_inc(v_a_1000_);
lean_dec_ref(v___x_999_);
v___x_1001_ = lean_unsigned_to_nat(0u);
v_bs_x27_1002_ = lean_array_uset(v_bs_987_, v_i_986_, v___x_1001_);
if (lean_obj_tag(v_a_1000_) == 6)
{
lean_object* v_val_1009_; lean_object* v_numFields_1010_; uint8_t v___x_1011_; lean_object* v___x_1012_; 
v_val_1009_ = lean_ctor_get(v_a_1000_, 0);
lean_inc_ref(v_val_1009_);
lean_dec_ref(v_a_1000_);
v_numFields_1010_ = lean_ctor_get(v_val_1009_, 4);
lean_inc(v_numFields_1010_);
lean_dec_ref(v_val_1009_);
v___x_1011_ = 0;
v___x_1012_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1012_, 0, v_numFields_1010_);
lean_ctor_set(v___x_1012_, 1, v___x_1001_);
lean_ctor_set_uint8(v___x_1012_, sizeof(void*)*2, v___x_1011_);
v_a_1004_ = v___x_1012_;
goto v___jp_1003_;
}
else
{
lean_object* v___x_1013_; lean_object* v___x_1014_; 
lean_dec(v_a_1000_);
v___x_1013_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5___closed__3);
lean_inc(v___y_994_);
lean_inc_ref(v___y_993_);
lean_inc(v___y_992_);
lean_inc_ref(v___y_991_);
lean_inc(v___y_990_);
lean_inc_ref(v___y_989_);
lean_inc(v___y_988_);
v___x_1014_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3(v___x_1013_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_);
if (lean_obj_tag(v___x_1014_) == 0)
{
lean_object* v_a_1015_; 
v_a_1015_ = lean_ctor_get(v___x_1014_, 0);
lean_inc(v_a_1015_);
lean_dec_ref(v___x_1014_);
v_a_1004_ = v_a_1015_;
goto v___jp_1003_;
}
else
{
lean_object* v_a_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1023_; 
lean_dec_ref(v_bs_x27_1002_);
lean_dec(v___y_994_);
lean_dec_ref(v___y_993_);
lean_dec(v___y_992_);
lean_dec_ref(v___y_991_);
lean_dec(v___y_990_);
lean_dec_ref(v___y_989_);
lean_dec(v___y_988_);
v_a_1016_ = lean_ctor_get(v___x_1014_, 0);
v_isSharedCheck_1023_ = !lean_is_exclusive(v___x_1014_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_1018_ = v___x_1014_;
v_isShared_1019_ = v_isSharedCheck_1023_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_a_1016_);
lean_dec(v___x_1014_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1023_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v___x_1021_; 
if (v_isShared_1019_ == 0)
{
v___x_1021_ = v___x_1018_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v_a_1016_);
v___x_1021_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
return v___x_1021_;
}
}
}
}
v___jp_1003_:
{
size_t v___x_1005_; size_t v___x_1006_; lean_object* v___x_1007_; 
v___x_1005_ = ((size_t)1ULL);
v___x_1006_ = lean_usize_add(v_i_986_, v___x_1005_);
v___x_1007_ = lean_array_uset(v_bs_x27_1002_, v_i_986_, v_a_1004_);
v_i_986_ = v___x_1006_;
v_bs_987_ = v___x_1007_;
goto _start;
}
}
else
{
lean_object* v_a_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1031_; 
lean_dec(v___y_994_);
lean_dec_ref(v___y_993_);
lean_dec(v___y_992_);
lean_dec_ref(v___y_991_);
lean_dec(v___y_990_);
lean_dec_ref(v___y_989_);
lean_dec(v___y_988_);
lean_dec_ref(v_bs_987_);
v_a_1024_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1026_ = v___x_999_;
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_a_1024_);
lean_dec(v___x_999_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___x_1029_; 
if (v_isShared_1027_ == 0)
{
v___x_1029_ = v___x_1026_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_a_1024_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5___boxed(lean_object* v_sz_1032_, lean_object* v_i_1033_, lean_object* v_bs_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_){
_start:
{
size_t v_sz_boxed_1043_; size_t v_i_boxed_1044_; lean_object* v_res_1045_; 
v_sz_boxed_1043_ = lean_unbox_usize(v_sz_1032_);
lean_dec(v_sz_1032_);
v_i_boxed_1044_ = lean_unbox_usize(v_i_1033_);
lean_dec(v_i_1033_);
v_res_1045_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5(v_sz_boxed_1043_, v_i_boxed_1044_, v_bs_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_);
return v_res_1045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__4___redArg(lean_object* v_declName_1046_, lean_object* v___y_1047_){
_start:
{
lean_object* v___x_1049_; lean_object* v_env_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1049_ = lean_st_ref_get(v___y_1047_);
v_env_1050_ = lean_ctor_get(v___x_1049_, 0);
lean_inc_ref(v_env_1050_);
lean_dec(v___x_1049_);
v___x_1051_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_1050_, v_declName_1046_);
v___x_1052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1051_);
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__4___redArg___boxed(lean_object* v_declName_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__4___redArg(v_declName_1053_, v___y_1054_);
lean_dec(v___y_1054_);
return v_res_1056_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1057_; lean_object* v_dummy_1058_; 
v___x_1057_ = lean_box(0);
v_dummy_1058_ = l_Lean_Expr_sort___override(v___x_1057_);
return v_dummy_1058_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1059_ = lean_box(0);
v___x_1060_ = lean_unsigned_to_nat(16u);
v___x_1061_ = lean_mk_array(v___x_1060_, v___x_1059_);
return v___x_1061_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1062_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__1, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__1_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__1);
v___x_1063_ = lean_unsigned_to_nat(0u);
v___x_1064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1063_);
lean_ctor_set(v___x_1064_, 1, v___x_1062_);
return v___x_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2(lean_object* v_e_1067_, uint8_t v_alsoCasesOn_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_){
_start:
{
uint8_t v___x_1080_; 
v___x_1080_ = l_Lean_Expr_isApp(v_e_1067_);
if (v___x_1080_ == 0)
{
lean_object* v___x_1081_; lean_object* v___x_1082_; 
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
lean_dec(v___y_1069_);
lean_dec_ref(v_e_1067_);
v___x_1081_ = lean_box(0);
v___x_1082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1081_);
return v___x_1082_;
}
else
{
lean_object* v___x_1083_; 
v___x_1083_ = l_Lean_Expr_getAppFn(v_e_1067_);
if (lean_obj_tag(v___x_1083_) == 4)
{
lean_object* v_declName_1084_; lean_object* v_us_1085_; lean_object* v___x_1086_; lean_object* v_a_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1241_; 
v_declName_1084_ = lean_ctor_get(v___x_1083_, 0);
lean_inc(v_declName_1084_);
v_us_1085_ = lean_ctor_get(v___x_1083_, 1);
lean_inc(v_us_1085_);
lean_dec_ref(v___x_1083_);
lean_inc(v_declName_1084_);
v___x_1086_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__4___redArg(v_declName_1084_, v___y_1075_);
v_a_1087_ = lean_ctor_get(v___x_1086_, 0);
v_isSharedCheck_1241_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1241_ == 0)
{
v___x_1089_ = v___x_1086_;
v_isShared_1090_ = v_isSharedCheck_1241_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_a_1087_);
lean_dec(v___x_1086_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1241_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
if (lean_obj_tag(v_a_1087_) == 1)
{
lean_object* v_val_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1133_; 
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
lean_dec(v___y_1069_);
v_val_1091_ = lean_ctor_get(v_a_1087_, 0);
v_isSharedCheck_1133_ = !lean_is_exclusive(v_a_1087_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1093_ = v_a_1087_;
v_isShared_1094_ = v_isSharedCheck_1133_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_val_1091_);
lean_dec(v_a_1087_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1133_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v_dummy_1095_; lean_object* v_nargs_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v_args_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; uint8_t v___x_1103_; 
v_dummy_1095_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0);
v_nargs_1096_ = l_Lean_Expr_getAppNumArgs(v_e_1067_);
lean_inc(v_nargs_1096_);
v___x_1097_ = lean_mk_array(v_nargs_1096_, v_dummy_1095_);
v___x_1098_ = lean_unsigned_to_nat(1u);
v___x_1099_ = lean_nat_sub(v_nargs_1096_, v___x_1098_);
lean_dec(v_nargs_1096_);
v_args_1100_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1067_, v___x_1097_, v___x_1099_);
v___x_1101_ = lean_array_get_size(v_args_1100_);
v___x_1102_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_1091_);
v___x_1103_ = lean_nat_dec_lt(v___x_1101_, v___x_1102_);
lean_dec(v___x_1102_);
if (v___x_1103_ == 0)
{
lean_object* v_numParams_1104_; lean_object* v_numDiscrs_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1124_; 
v_numParams_1104_ = lean_ctor_get(v_val_1091_, 0);
v_numDiscrs_1105_ = lean_ctor_get(v_val_1091_, 1);
v___x_1106_ = lean_array_mk(v_us_1085_);
v___x_1107_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1104_);
v___x_1108_ = l_Array_extract___redArg(v_args_1100_, v___x_1107_, v_numParams_1104_);
v___x_1109_ = l_Lean_instInhabitedExpr;
v___x_1110_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_1091_);
v___x_1111_ = lean_array_get(v___x_1109_, v_args_1100_, v___x_1110_);
lean_dec(v___x_1110_);
v___x_1112_ = lean_nat_add(v_numParams_1104_, v___x_1098_);
v___x_1113_ = lean_nat_add(v___x_1112_, v_numDiscrs_1105_);
lean_inc(v___x_1113_);
lean_inc_ref(v_args_1100_);
v___x_1114_ = l_Array_toSubarray___redArg(v_args_1100_, v___x_1112_, v___x_1113_);
v___x_1115_ = l_Subarray_copy___redArg(v___x_1114_);
v___x_1116_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_1091_);
v___x_1117_ = lean_nat_add(v___x_1113_, v___x_1116_);
lean_dec(v___x_1116_);
lean_inc(v___x_1117_);
lean_inc_ref(v_args_1100_);
v___x_1118_ = l_Array_toSubarray___redArg(v_args_1100_, v___x_1113_, v___x_1117_);
v___x_1119_ = l_Subarray_copy___redArg(v___x_1118_);
v___x_1120_ = l_Array_toSubarray___redArg(v_args_1100_, v___x_1117_, v___x_1101_);
v___x_1121_ = l_Subarray_copy___redArg(v___x_1120_);
v___x_1122_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1122_, 0, v_val_1091_);
lean_ctor_set(v___x_1122_, 1, v_declName_1084_);
lean_ctor_set(v___x_1122_, 2, v___x_1106_);
lean_ctor_set(v___x_1122_, 3, v___x_1108_);
lean_ctor_set(v___x_1122_, 4, v___x_1111_);
lean_ctor_set(v___x_1122_, 5, v___x_1115_);
lean_ctor_set(v___x_1122_, 6, v___x_1119_);
lean_ctor_set(v___x_1122_, 7, v___x_1121_);
if (v_isShared_1094_ == 0)
{
lean_ctor_set(v___x_1093_, 0, v___x_1122_);
v___x_1124_ = v___x_1093_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v___x_1122_);
v___x_1124_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
lean_object* v___x_1126_; 
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 0, v___x_1124_);
v___x_1126_ = v___x_1089_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v___x_1124_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
}
else
{
lean_object* v___x_1129_; lean_object* v___x_1131_; 
lean_dec_ref(v_args_1100_);
lean_del_object(v___x_1093_);
lean_dec(v_val_1091_);
lean_dec(v_us_1085_);
lean_dec(v_declName_1084_);
v___x_1129_ = lean_box(0);
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 0, v___x_1129_);
v___x_1131_ = v___x_1089_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v___x_1129_);
v___x_1131_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
return v___x_1131_;
}
}
}
}
else
{
lean_object* v___x_1134_; 
lean_del_object(v___x_1089_);
lean_dec(v_a_1087_);
v___x_1134_ = lean_st_ref_get(v___y_1075_);
if (v_alsoCasesOn_1068_ == 0)
{
lean_dec(v___x_1134_);
lean_dec(v_us_1085_);
lean_dec(v_declName_1084_);
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
lean_dec(v___y_1069_);
lean_dec_ref(v_e_1067_);
goto v___jp_1077_;
}
else
{
lean_object* v_env_1135_; uint8_t v___x_1136_; 
v_env_1135_ = lean_ctor_get(v___x_1134_, 0);
lean_inc_ref(v_env_1135_);
lean_dec(v___x_1134_);
lean_inc(v_declName_1084_);
v___x_1136_ = l_Lean_isCasesOnRecursor(v_env_1135_, v_declName_1084_);
if (v___x_1136_ == 0)
{
lean_dec(v_us_1085_);
lean_dec(v_declName_1084_);
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
lean_dec(v___y_1069_);
lean_dec_ref(v_e_1067_);
goto v___jp_1077_;
}
else
{
lean_object* v_indName_1137_; lean_object* v___x_1138_; 
v_indName_1137_ = l_Lean_Name_getPrefix(v_declName_1084_);
lean_inc_ref(v___y_1074_);
v___x_1138_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2(v_indName_1137_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_);
if (lean_obj_tag(v___x_1138_) == 0)
{
lean_object* v_a_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1232_; 
v_a_1139_ = lean_ctor_get(v___x_1138_, 0);
v_isSharedCheck_1232_ = !lean_is_exclusive(v___x_1138_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1141_ = v___x_1138_;
v_isShared_1142_ = v_isSharedCheck_1232_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_a_1139_);
lean_dec(v___x_1138_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1232_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
if (lean_obj_tag(v_a_1139_) == 5)
{
lean_object* v_val_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1227_; 
v_val_1143_ = lean_ctor_get(v_a_1139_, 0);
v_isSharedCheck_1227_ = !lean_is_exclusive(v_a_1139_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1145_ = v_a_1139_;
v_isShared_1146_ = v_isSharedCheck_1227_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_val_1143_);
lean_dec(v_a_1139_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1227_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v_toConstantVal_1147_; lean_object* v_numParams_1148_; lean_object* v_numIndices_1149_; lean_object* v_ctors_1150_; lean_object* v_nargs_1151_; lean_object* v_dummy_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v_args_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; uint8_t v___x_1163_; 
v_toConstantVal_1147_ = lean_ctor_get(v_val_1143_, 0);
lean_inc_ref(v_toConstantVal_1147_);
v_numParams_1148_ = lean_ctor_get(v_val_1143_, 1);
lean_inc(v_numParams_1148_);
v_numIndices_1149_ = lean_ctor_get(v_val_1143_, 2);
lean_inc(v_numIndices_1149_);
v_ctors_1150_ = lean_ctor_get(v_val_1143_, 4);
lean_inc(v_ctors_1150_);
v_nargs_1151_ = l_Lean_Expr_getAppNumArgs(v_e_1067_);
v_dummy_1152_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0);
lean_inc(v_nargs_1151_);
v___x_1153_ = lean_mk_array(v_nargs_1151_, v_dummy_1152_);
v___x_1154_ = lean_unsigned_to_nat(1u);
v___x_1155_ = lean_nat_sub(v_nargs_1151_, v___x_1154_);
lean_dec(v_nargs_1151_);
v_args_1156_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1067_, v___x_1153_, v___x_1155_);
v___x_1157_ = lean_nat_add(v_numParams_1148_, v___x_1154_);
v___x_1158_ = lean_nat_add(v___x_1157_, v_numIndices_1149_);
v___x_1159_ = lean_nat_add(v___x_1158_, v___x_1154_);
lean_dec(v___x_1158_);
v___x_1160_ = l_Lean_InductiveVal_numCtors(v_val_1143_);
lean_dec_ref(v_val_1143_);
v___x_1161_ = lean_nat_add(v___x_1159_, v___x_1160_);
lean_dec(v___x_1160_);
v___x_1162_ = lean_array_get_size(v_args_1156_);
v___x_1163_ = lean_nat_dec_le(v___x_1161_, v___x_1162_);
if (v___x_1163_ == 0)
{
lean_object* v___x_1164_; lean_object* v___x_1166_; 
lean_dec(v___x_1161_);
lean_dec(v___x_1159_);
lean_dec(v___x_1157_);
lean_dec_ref(v_args_1156_);
lean_dec(v_ctors_1150_);
lean_dec(v_numIndices_1149_);
lean_dec(v_numParams_1148_);
lean_dec_ref(v_toConstantVal_1147_);
lean_del_object(v___x_1145_);
lean_dec(v_us_1085_);
lean_dec(v_declName_1084_);
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
lean_dec(v___y_1069_);
v___x_1164_ = lean_box(0);
if (v_isShared_1142_ == 0)
{
lean_ctor_set(v___x_1141_, 0, v___x_1164_);
v___x_1166_ = v___x_1141_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v___x_1164_);
v___x_1166_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
return v___x_1166_;
}
}
else
{
lean_object* v___x_1168_; lean_object* v_params_1169_; lean_object* v___x_1170_; lean_object* v_motive_1171_; lean_object* v_discrs_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v_discrInfos_1175_; lean_object* v_alts_1176_; lean_object* v___y_1178_; lean_object* v___y_1179_; lean_object* v_lower_1218_; lean_object* v_upper_1219_; uint8_t v___x_1226_; 
lean_del_object(v___x_1141_);
v___x_1168_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1148_);
lean_inc_ref(v_args_1156_);
v_params_1169_ = l_Array_toSubarray___redArg(v_args_1156_, v___x_1168_, v_numParams_1148_);
v___x_1170_ = l_Lean_instInhabitedExpr;
v_motive_1171_ = lean_array_get(v___x_1170_, v_args_1156_, v_numParams_1148_);
lean_dec(v_numParams_1148_);
lean_inc(v___x_1159_);
lean_inc_ref(v_args_1156_);
v_discrs_1172_ = l_Array_toSubarray___redArg(v_args_1156_, v___x_1157_, v___x_1159_);
v___x_1173_ = lean_nat_add(v_numIndices_1149_, v___x_1154_);
lean_dec(v_numIndices_1149_);
v___x_1174_ = lean_box(0);
v_discrInfos_1175_ = lean_mk_array(v___x_1173_, v___x_1174_);
lean_inc(v___x_1161_);
lean_inc_ref(v_args_1156_);
v_alts_1176_ = l_Array_toSubarray___redArg(v_args_1156_, v___x_1159_, v___x_1161_);
v___x_1226_ = lean_nat_dec_le(v___x_1161_, v___x_1168_);
if (v___x_1226_ == 0)
{
v_lower_1218_ = v___x_1161_;
v_upper_1219_ = v___x_1162_;
goto v___jp_1217_;
}
else
{
lean_dec(v___x_1161_);
v_lower_1218_ = v___x_1168_;
v_upper_1219_ = v___x_1162_;
goto v___jp_1217_;
}
v___jp_1177_:
{
lean_object* v___x_1180_; size_t v_sz_1181_; size_t v___x_1182_; lean_object* v___x_1183_; 
v___x_1180_ = lean_array_mk(v_ctors_1150_);
v_sz_1181_ = lean_array_size(v___x_1180_);
v___x_1182_ = ((size_t)0ULL);
v___x_1183_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5(v_sz_1181_, v___x_1182_, v___x_1180_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_);
if (lean_obj_tag(v___x_1183_) == 0)
{
lean_object* v_a_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1208_; 
v_a_1184_ = lean_ctor_get(v___x_1183_, 0);
v_isSharedCheck_1208_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1186_ = v___x_1183_;
v_isShared_1187_ = v_isSharedCheck_1208_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_a_1184_);
lean_dec(v___x_1183_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1208_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v_start_1188_; lean_object* v_stop_1189_; lean_object* v_start_1190_; lean_object* v_stop_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1203_; 
v_start_1188_ = lean_ctor_get(v_params_1169_, 1);
lean_inc(v_start_1188_);
v_stop_1189_ = lean_ctor_get(v_params_1169_, 2);
lean_inc(v_stop_1189_);
v_start_1190_ = lean_ctor_get(v_discrs_1172_, 1);
lean_inc(v_start_1190_);
v_stop_1191_ = lean_ctor_get(v_discrs_1172_, 2);
lean_inc(v_stop_1191_);
v___x_1192_ = lean_nat_sub(v_stop_1189_, v_start_1188_);
lean_dec(v_start_1188_);
lean_dec(v_stop_1189_);
v___x_1193_ = lean_nat_sub(v_stop_1191_, v_start_1190_);
lean_dec(v_start_1190_);
lean_dec(v_stop_1191_);
v___x_1194_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__2, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__2_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__2);
v___x_1195_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1192_);
lean_ctor_set(v___x_1195_, 1, v___x_1193_);
lean_ctor_set(v___x_1195_, 2, v_a_1184_);
lean_ctor_set(v___x_1195_, 3, v___y_1179_);
lean_ctor_set(v___x_1195_, 4, v_discrInfos_1175_);
lean_ctor_set(v___x_1195_, 5, v___x_1194_);
v___x_1196_ = lean_array_mk(v_us_1085_);
v___x_1197_ = l_Subarray_copy___redArg(v_params_1169_);
v___x_1198_ = l_Subarray_copy___redArg(v_discrs_1172_);
v___x_1199_ = l_Subarray_copy___redArg(v_alts_1176_);
v___x_1200_ = l_Subarray_copy___redArg(v___y_1178_);
v___x_1201_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1201_, 0, v___x_1195_);
lean_ctor_set(v___x_1201_, 1, v_declName_1084_);
lean_ctor_set(v___x_1201_, 2, v___x_1196_);
lean_ctor_set(v___x_1201_, 3, v___x_1197_);
lean_ctor_set(v___x_1201_, 4, v_motive_1171_);
lean_ctor_set(v___x_1201_, 5, v___x_1198_);
lean_ctor_set(v___x_1201_, 6, v___x_1199_);
lean_ctor_set(v___x_1201_, 7, v___x_1200_);
if (v_isShared_1146_ == 0)
{
lean_ctor_set_tag(v___x_1145_, 1);
lean_ctor_set(v___x_1145_, 0, v___x_1201_);
v___x_1203_ = v___x_1145_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v___x_1201_);
v___x_1203_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
lean_object* v___x_1205_; 
if (v_isShared_1187_ == 0)
{
lean_ctor_set(v___x_1186_, 0, v___x_1203_);
v___x_1205_ = v___x_1186_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v___x_1203_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
}
}
else
{
lean_object* v_a_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1216_; 
lean_dec(v___y_1179_);
lean_dec_ref(v___y_1178_);
lean_dec_ref(v_alts_1176_);
lean_dec_ref(v_discrInfos_1175_);
lean_dec_ref(v_discrs_1172_);
lean_dec(v_motive_1171_);
lean_dec_ref(v_params_1169_);
lean_del_object(v___x_1145_);
lean_dec(v_us_1085_);
lean_dec(v_declName_1084_);
v_a_1209_ = lean_ctor_get(v___x_1183_, 0);
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1211_ = v___x_1183_;
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_a_1209_);
lean_dec(v___x_1183_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1214_; 
if (v_isShared_1212_ == 0)
{
v___x_1214_ = v___x_1211_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_a_1209_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
}
}
v___jp_1217_:
{
lean_object* v_levelParams_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; uint8_t v___x_1224_; 
v_levelParams_1220_ = lean_ctor_get(v_toConstantVal_1147_, 1);
lean_inc(v_levelParams_1220_);
lean_dec_ref(v_toConstantVal_1147_);
v___x_1221_ = l_Array_toSubarray___redArg(v_args_1156_, v_lower_1218_, v_upper_1219_);
v___x_1222_ = l_List_lengthTR___redArg(v_levelParams_1220_);
lean_dec(v_levelParams_1220_);
v___x_1223_ = l_List_lengthTR___redArg(v_us_1085_);
v___x_1224_ = lean_nat_dec_eq(v___x_1222_, v___x_1223_);
lean_dec(v___x_1223_);
lean_dec(v___x_1222_);
if (v___x_1224_ == 0)
{
lean_object* v___x_1225_; 
v___x_1225_ = ((lean_object*)(l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__3));
v___y_1178_ = v___x_1221_;
v___y_1179_ = v___x_1225_;
goto v___jp_1177_;
}
else
{
v___y_1178_ = v___x_1221_;
v___y_1179_ = v___x_1174_;
goto v___jp_1177_;
}
}
}
}
}
else
{
lean_object* v___x_1228_; lean_object* v___x_1230_; 
lean_dec(v_a_1139_);
lean_dec(v_us_1085_);
lean_dec(v_declName_1084_);
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
lean_dec(v___y_1069_);
lean_dec_ref(v_e_1067_);
v___x_1228_ = lean_box(0);
if (v_isShared_1142_ == 0)
{
lean_ctor_set(v___x_1141_, 0, v___x_1228_);
v___x_1230_ = v___x_1141_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v___x_1228_);
v___x_1230_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
return v___x_1230_;
}
}
}
}
else
{
lean_object* v_a_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1240_; 
lean_dec(v_us_1085_);
lean_dec(v_declName_1084_);
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
lean_dec(v___y_1069_);
lean_dec_ref(v_e_1067_);
v_a_1233_ = lean_ctor_get(v___x_1138_, 0);
v_isSharedCheck_1240_ = !lean_is_exclusive(v___x_1138_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1235_ = v___x_1138_;
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_a_1233_);
lean_dec(v___x_1138_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v___x_1238_; 
if (v_isShared_1236_ == 0)
{
v___x_1238_ = v___x_1235_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_a_1233_);
v___x_1238_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
return v___x_1238_;
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
lean_dec_ref(v___x_1083_);
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
lean_dec(v___y_1069_);
lean_dec_ref(v_e_1067_);
goto v___jp_1077_;
}
}
v___jp_1077_:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1078_ = lean_box(0);
v___x_1079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1078_);
return v___x_1079_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___boxed(lean_object* v_e_1242_, lean_object* v_alsoCasesOn_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_){
_start:
{
uint8_t v_alsoCasesOn_boxed_1252_; lean_object* v_res_1253_; 
v_alsoCasesOn_boxed_1252_ = lean_unbox(v_alsoCasesOn_1243_);
v_res_1253_ = l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2(v_e_1242_, v_alsoCasesOn_boxed_1252_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_);
return v_res_1253_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__5(size_t v_sz_1254_, size_t v_i_1255_, lean_object* v_bs_1256_){
_start:
{
uint8_t v___x_1257_; 
v___x_1257_ = lean_usize_dec_lt(v_i_1255_, v_sz_1254_);
if (v___x_1257_ == 0)
{
return v_bs_1256_;
}
else
{
lean_object* v_v_1258_; lean_object* v___x_1259_; lean_object* v_bs_x27_1260_; lean_object* v___y_1262_; lean_object* v___x_1267_; 
v_v_1258_ = lean_array_uget(v_bs_1256_, v_i_1255_);
v___x_1259_ = lean_unsigned_to_nat(0u);
v_bs_x27_1260_ = lean_array_uset(v_bs_1256_, v_i_1255_, v___x_1259_);
v___x_1267_ = l_Lean_Elab_WF_isWfParam_x3f(v_v_1258_);
if (lean_obj_tag(v___x_1267_) == 0)
{
v___y_1262_ = v_v_1258_;
goto v___jp_1261_;
}
else
{
lean_object* v_val_1268_; 
lean_dec(v_v_1258_);
v_val_1268_ = lean_ctor_get(v___x_1267_, 0);
lean_inc(v_val_1268_);
lean_dec_ref(v___x_1267_);
v___y_1262_ = v_val_1268_;
goto v___jp_1261_;
}
v___jp_1261_:
{
size_t v___x_1263_; size_t v___x_1264_; lean_object* v___x_1265_; 
v___x_1263_ = ((size_t)1ULL);
v___x_1264_ = lean_usize_add(v_i_1255_, v___x_1263_);
v___x_1265_ = lean_array_uset(v_bs_x27_1260_, v_i_1255_, v___y_1262_);
v_i_1255_ = v___x_1264_;
v_bs_1256_ = v___x_1265_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__5___boxed(lean_object* v_sz_1269_, lean_object* v_i_1270_, lean_object* v_bs_1271_){
_start:
{
size_t v_sz_boxed_1272_; size_t v_i_boxed_1273_; lean_object* v_res_1274_; 
v_sz_boxed_1272_ = lean_unbox_usize(v_sz_1269_);
lean_dec(v_sz_1269_);
v_i_boxed_1273_ = lean_unbox_usize(v_i_1270_);
lean_dec(v_i_1270_);
v_res_1274_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__5(v_sz_boxed_1272_, v_i_boxed_1273_, v_bs_1271_);
return v_res_1274_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_WF_paramMatcher_spec__3(lean_object* v_as_1275_, size_t v_i_1276_, size_t v_stop_1277_){
_start:
{
uint8_t v___x_1278_; 
v___x_1278_ = lean_usize_dec_eq(v_i_1276_, v_stop_1277_);
if (v___x_1278_ == 0)
{
uint8_t v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; 
v___x_1279_ = 1;
v___x_1280_ = lean_array_uget_borrowed(v_as_1275_, v_i_1276_);
v___x_1281_ = l_Lean_Elab_WF_isWfParam_x3f(v___x_1280_);
if (lean_obj_tag(v___x_1281_) == 0)
{
if (v___x_1278_ == 0)
{
size_t v___x_1282_; size_t v___x_1283_; 
v___x_1282_ = ((size_t)1ULL);
v___x_1283_ = lean_usize_add(v_i_1276_, v___x_1282_);
v_i_1276_ = v___x_1283_;
goto _start;
}
else
{
return v___x_1279_;
}
}
else
{
lean_dec_ref(v___x_1281_);
return v___x_1279_;
}
}
else
{
uint8_t v___x_1285_; 
v___x_1285_ = 0;
return v___x_1285_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_WF_paramMatcher_spec__3___boxed(lean_object* v_as_1286_, lean_object* v_i_1287_, lean_object* v_stop_1288_){
_start:
{
size_t v_i_boxed_1289_; size_t v_stop_boxed_1290_; uint8_t v_res_1291_; lean_object* v_r_1292_; 
v_i_boxed_1289_ = lean_unbox_usize(v_i_1287_);
lean_dec(v_i_1287_);
v_stop_boxed_1290_ = lean_unbox_usize(v_stop_1288_);
lean_dec(v_stop_1288_);
v_res_1291_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_WF_paramMatcher_spec__3(v_as_1286_, v_i_boxed_1289_, v_stop_boxed_1290_);
lean_dec_ref(v_as_1286_);
v_r_1292_ = lean_box(v_res_1291_);
return v_r_1292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramMatcher(lean_object* v_e_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_){
_start:
{
uint8_t v___x_1302_; lean_object* v___x_1303_; 
v___x_1302_ = 1;
lean_inc(v_a_1300_);
lean_inc_ref(v_a_1299_);
lean_inc(v_a_1298_);
lean_inc_ref(v_a_1297_);
lean_inc(v_a_1296_);
lean_inc_ref(v_a_1295_);
lean_inc(v_a_1294_);
v___x_1303_ = l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2(v_e_1293_, v___x_1302_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_);
if (lean_obj_tag(v___x_1303_) == 0)
{
lean_object* v_a_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1366_; 
v_a_1304_ = lean_ctor_get(v___x_1303_, 0);
v_isSharedCheck_1366_ = !lean_is_exclusive(v___x_1303_);
if (v_isSharedCheck_1366_ == 0)
{
v___x_1306_ = v___x_1303_;
v_isShared_1307_ = v_isSharedCheck_1366_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_a_1304_);
lean_dec(v___x_1303_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1366_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
if (lean_obj_tag(v_a_1304_) == 1)
{
lean_object* v_val_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1363_; 
v_val_1313_ = lean_ctor_get(v_a_1304_, 0);
v_isSharedCheck_1363_ = !lean_is_exclusive(v_a_1304_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1315_ = v_a_1304_;
v_isShared_1316_ = v_isSharedCheck_1363_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_val_1313_);
lean_dec(v_a_1304_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1363_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v_toMatcherInfo_1317_; lean_object* v_matcherName_1318_; lean_object* v_matcherLevels_1319_; lean_object* v_params_1320_; lean_object* v_motive_1321_; lean_object* v_discrs_1322_; lean_object* v_alts_1323_; lean_object* v_remaining_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1362_; 
v_toMatcherInfo_1317_ = lean_ctor_get(v_val_1313_, 0);
v_matcherName_1318_ = lean_ctor_get(v_val_1313_, 1);
v_matcherLevels_1319_ = lean_ctor_get(v_val_1313_, 2);
v_params_1320_ = lean_ctor_get(v_val_1313_, 3);
v_motive_1321_ = lean_ctor_get(v_val_1313_, 4);
v_discrs_1322_ = lean_ctor_get(v_val_1313_, 5);
v_alts_1323_ = lean_ctor_get(v_val_1313_, 6);
v_remaining_1324_ = lean_ctor_get(v_val_1313_, 7);
v_isSharedCheck_1362_ = !lean_is_exclusive(v_val_1313_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1326_ = v_val_1313_;
v_isShared_1327_ = v_isSharedCheck_1362_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_remaining_1324_);
lean_inc(v_alts_1323_);
lean_inc(v_discrs_1322_);
lean_inc(v_motive_1321_);
lean_inc(v_params_1320_);
lean_inc(v_matcherLevels_1319_);
lean_inc(v_matcherName_1318_);
lean_inc(v_toMatcherInfo_1317_);
lean_dec(v_val_1313_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1362_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; uint8_t v___x_1330_; 
v___x_1328_ = lean_unsigned_to_nat(0u);
v___x_1329_ = lean_array_get_size(v_discrs_1322_);
v___x_1330_ = lean_nat_dec_lt(v___x_1328_, v___x_1329_);
if (v___x_1330_ == 0)
{
lean_del_object(v___x_1326_);
lean_dec_ref(v_remaining_1324_);
lean_dec_ref(v_alts_1323_);
lean_dec_ref(v_discrs_1322_);
lean_dec_ref(v_motive_1321_);
lean_dec_ref(v_params_1320_);
lean_dec_ref(v_matcherLevels_1319_);
lean_dec(v_matcherName_1318_);
lean_dec_ref(v_toMatcherInfo_1317_);
lean_del_object(v___x_1315_);
lean_dec(v_a_1300_);
lean_dec_ref(v_a_1299_);
lean_dec(v_a_1298_);
lean_dec_ref(v_a_1297_);
lean_dec(v_a_1296_);
lean_dec_ref(v_a_1295_);
lean_dec(v_a_1294_);
goto v___jp_1308_;
}
else
{
if (v___x_1330_ == 0)
{
lean_del_object(v___x_1326_);
lean_dec_ref(v_remaining_1324_);
lean_dec_ref(v_alts_1323_);
lean_dec_ref(v_discrs_1322_);
lean_dec_ref(v_motive_1321_);
lean_dec_ref(v_params_1320_);
lean_dec_ref(v_matcherLevels_1319_);
lean_dec(v_matcherName_1318_);
lean_dec_ref(v_toMatcherInfo_1317_);
lean_del_object(v___x_1315_);
lean_dec(v_a_1300_);
lean_dec_ref(v_a_1299_);
lean_dec(v_a_1298_);
lean_dec_ref(v_a_1297_);
lean_dec(v_a_1296_);
lean_dec_ref(v_a_1295_);
lean_dec(v_a_1294_);
goto v___jp_1308_;
}
else
{
size_t v___x_1331_; size_t v___x_1332_; uint8_t v___x_1333_; 
v___x_1331_ = ((size_t)0ULL);
v___x_1332_ = lean_usize_of_nat(v___x_1329_);
v___x_1333_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_WF_paramMatcher_spec__3(v_discrs_1322_, v___x_1331_, v___x_1332_);
if (v___x_1333_ == 0)
{
lean_del_object(v___x_1326_);
lean_dec_ref(v_remaining_1324_);
lean_dec_ref(v_alts_1323_);
lean_dec_ref(v_discrs_1322_);
lean_dec_ref(v_motive_1321_);
lean_dec_ref(v_params_1320_);
lean_dec_ref(v_matcherLevels_1319_);
lean_dec(v_matcherName_1318_);
lean_dec_ref(v_toMatcherInfo_1317_);
lean_del_object(v___x_1315_);
lean_dec(v_a_1300_);
lean_dec_ref(v_a_1299_);
lean_dec(v_a_1298_);
lean_dec_ref(v_a_1297_);
lean_dec(v_a_1296_);
lean_dec_ref(v_a_1295_);
lean_dec(v_a_1294_);
goto v___jp_1308_;
}
else
{
size_t v_sz_1334_; lean_object* v___x_1335_; 
lean_del_object(v___x_1306_);
v_sz_1334_ = lean_array_size(v_alts_1323_);
v___x_1335_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__4(v_sz_1334_, v___x_1331_, v_alts_1323_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_);
if (lean_obj_tag(v___x_1335_) == 0)
{
lean_object* v_a_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1353_; 
v_a_1336_ = lean_ctor_get(v___x_1335_, 0);
v_isSharedCheck_1353_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1338_ = v___x_1335_;
v_isShared_1339_ = v_isSharedCheck_1353_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_a_1336_);
lean_dec(v___x_1335_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1353_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
size_t v_sz_1340_; lean_object* v___x_1341_; lean_object* v___x_1343_; 
v_sz_1340_ = lean_array_size(v_discrs_1322_);
v___x_1341_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__5(v_sz_1340_, v___x_1331_, v_discrs_1322_);
if (v_isShared_1327_ == 0)
{
lean_ctor_set(v___x_1326_, 6, v_a_1336_);
lean_ctor_set(v___x_1326_, 5, v___x_1341_);
v___x_1343_ = v___x_1326_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v_toMatcherInfo_1317_);
lean_ctor_set(v_reuseFailAlloc_1352_, 1, v_matcherName_1318_);
lean_ctor_set(v_reuseFailAlloc_1352_, 2, v_matcherLevels_1319_);
lean_ctor_set(v_reuseFailAlloc_1352_, 3, v_params_1320_);
lean_ctor_set(v_reuseFailAlloc_1352_, 4, v_motive_1321_);
lean_ctor_set(v_reuseFailAlloc_1352_, 5, v___x_1341_);
lean_ctor_set(v_reuseFailAlloc_1352_, 6, v_a_1336_);
lean_ctor_set(v_reuseFailAlloc_1352_, 7, v_remaining_1324_);
v___x_1343_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
lean_object* v___x_1344_; lean_object* v___x_1346_; 
v___x_1344_ = l_Lean_Meta_MatcherApp_toExpr(v___x_1343_);
if (v_isShared_1316_ == 0)
{
lean_ctor_set(v___x_1315_, 0, v___x_1344_);
v___x_1346_ = v___x_1315_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v___x_1344_);
v___x_1346_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
lean_object* v___x_1347_; lean_object* v___x_1349_; 
v___x_1347_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1347_, 0, v___x_1346_);
if (v_isShared_1339_ == 0)
{
lean_ctor_set(v___x_1338_, 0, v___x_1347_);
v___x_1349_ = v___x_1338_;
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
}
else
{
lean_object* v_a_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1361_; 
lean_del_object(v___x_1326_);
lean_dec_ref(v_remaining_1324_);
lean_dec_ref(v_discrs_1322_);
lean_dec_ref(v_motive_1321_);
lean_dec_ref(v_params_1320_);
lean_dec_ref(v_matcherLevels_1319_);
lean_dec(v_matcherName_1318_);
lean_dec_ref(v_toMatcherInfo_1317_);
lean_del_object(v___x_1315_);
v_a_1354_ = lean_ctor_get(v___x_1335_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1356_ = v___x_1335_;
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_a_1354_);
lean_dec(v___x_1335_);
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
}
}
}
}
else
{
lean_object* v___x_1364_; lean_object* v___x_1365_; 
lean_del_object(v___x_1306_);
lean_dec(v_a_1304_);
lean_dec(v_a_1300_);
lean_dec_ref(v_a_1299_);
lean_dec(v_a_1298_);
lean_dec_ref(v_a_1297_);
lean_dec(v_a_1296_);
lean_dec_ref(v_a_1295_);
lean_dec(v_a_1294_);
v___x_1364_ = ((lean_object*)(l_Lean_Elab_WF_paramProj___closed__0));
v___x_1365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1365_, 0, v___x_1364_);
return v___x_1365_;
}
v___jp_1308_:
{
lean_object* v___x_1309_; lean_object* v___x_1311_; 
v___x_1309_ = ((lean_object*)(l_Lean_Elab_WF_paramProj___closed__0));
if (v_isShared_1307_ == 0)
{
lean_ctor_set(v___x_1306_, 0, v___x_1309_);
v___x_1311_ = v___x_1306_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v___x_1309_);
v___x_1311_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
return v___x_1311_;
}
}
}
}
else
{
lean_object* v_a_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1374_; 
lean_dec(v_a_1300_);
lean_dec_ref(v_a_1299_);
lean_dec(v_a_1298_);
lean_dec_ref(v_a_1297_);
lean_dec(v_a_1296_);
lean_dec_ref(v_a_1295_);
lean_dec(v_a_1294_);
v_a_1367_ = lean_ctor_get(v___x_1303_, 0);
v_isSharedCheck_1374_ = !lean_is_exclusive(v___x_1303_);
if (v_isSharedCheck_1374_ == 0)
{
v___x_1369_ = v___x_1303_;
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_a_1367_);
lean_dec(v___x_1303_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1372_; 
if (v_isShared_1370_ == 0)
{
v___x_1372_ = v___x_1369_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v_a_1367_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
return v___x_1372_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramMatcher___boxed(lean_object* v_e_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_){
_start:
{
lean_object* v_res_1384_; 
v_res_1384_ = l_Lean_Elab_WF_paramMatcher(v_e_1375_, v_a_1376_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_, v_a_1381_, v_a_1382_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__0(size_t v_sz_1385_, size_t v_i_1386_, lean_object* v_bs_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_){
_start:
{
lean_object* v___x_1396_; 
v___x_1396_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__0___redArg(v_sz_1385_, v_i_1386_, v_bs_1387_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_);
return v___x_1396_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__0___boxed(lean_object* v_sz_1397_, lean_object* v_i_1398_, lean_object* v_bs_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_){
_start:
{
size_t v_sz_boxed_1408_; size_t v_i_boxed_1409_; lean_object* v_res_1410_; 
v_sz_boxed_1408_ = lean_unbox_usize(v_sz_1397_);
lean_dec(v_sz_1397_);
v_i_boxed_1409_ = lean_unbox_usize(v_i_1398_);
lean_dec(v_i_1398_);
v_res_1410_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__0(v_sz_boxed_1408_, v_i_boxed_1409_, v_bs_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_);
lean_dec(v___y_1402_);
lean_dec_ref(v___y_1401_);
lean_dec(v___y_1400_);
return v_res_1410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__4(lean_object* v_declName_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_){
_start:
{
lean_object* v___x_1420_; 
v___x_1420_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__4___redArg(v_declName_1411_, v___y_1418_);
return v___x_1420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__4___boxed(lean_object* v_declName_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_){
_start:
{
lean_object* v_res_1430_; 
v_res_1430_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__4(v_declName_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_);
lean_dec(v___y_1428_);
lean_dec_ref(v___y_1427_);
lean_dec(v___y_1426_);
lean_dec_ref(v___y_1425_);
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
lean_dec(v___y_1422_);
return v_res_1430_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3(lean_object* v_00_u03b1_1431_, lean_object* v_constName_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_){
_start:
{
lean_object* v___x_1441_; 
v___x_1441_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3___redArg(v_constName_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_);
return v___x_1441_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1442_, lean_object* v_constName_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_){
_start:
{
lean_object* v_res_1452_; 
v_res_1452_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3(v_00_u03b1_1442_, v_constName_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_);
lean_dec(v___y_1450_);
lean_dec(v___y_1448_);
lean_dec_ref(v___y_1447_);
lean_dec(v___y_1446_);
lean_dec_ref(v___y_1445_);
lean_dec(v___y_1444_);
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9(lean_object* v_00_u03b1_1453_, lean_object* v_ref_1454_, lean_object* v_constName_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_){
_start:
{
lean_object* v___x_1464_; 
v___x_1464_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg(v_ref_1454_, v_constName_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_);
return v___x_1464_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___boxed(lean_object* v_00_u03b1_1465_, lean_object* v_ref_1466_, lean_object* v_constName_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_){
_start:
{
lean_object* v_res_1476_; 
v_res_1476_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9(v_00_u03b1_1465_, v_ref_1466_, v_constName_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_);
lean_dec(v___y_1474_);
lean_dec(v___y_1472_);
lean_dec_ref(v___y_1471_);
lean_dec(v___y_1470_);
lean_dec_ref(v___y_1469_);
lean_dec(v___y_1468_);
lean_dec(v_ref_1466_);
return v_res_1476_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11(lean_object* v_00_u03b1_1477_, lean_object* v_ref_1478_, lean_object* v_msg_1479_, lean_object* v_declHint_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_){
_start:
{
lean_object* v___x_1489_; 
v___x_1489_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11___redArg(v_ref_1478_, v_msg_1479_, v_declHint_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_);
return v___x_1489_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11___boxed(lean_object* v_00_u03b1_1490_, lean_object* v_ref_1491_, lean_object* v_msg_1492_, lean_object* v_declHint_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_){
_start:
{
lean_object* v_res_1502_; 
v_res_1502_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11(v_00_u03b1_1490_, v_ref_1491_, v_msg_1492_, v_declHint_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_);
lean_dec(v___y_1500_);
lean_dec(v___y_1498_);
lean_dec_ref(v___y_1497_);
lean_dec(v___y_1496_);
lean_dec_ref(v___y_1495_);
lean_dec(v___y_1494_);
lean_dec(v_ref_1491_);
return v_res_1502_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13(lean_object* v_msg_1503_, lean_object* v_declHint_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_){
_start:
{
lean_object* v___x_1513_; 
v___x_1513_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg(v_msg_1503_, v_declHint_1504_, v___y_1511_);
return v___x_1513_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___boxed(lean_object* v_msg_1514_, lean_object* v_declHint_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_){
_start:
{
lean_object* v_res_1524_; 
v_res_1524_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13(v_msg_1514_, v_declHint_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
lean_dec(v___y_1522_);
lean_dec_ref(v___y_1521_);
lean_dec(v___y_1520_);
lean_dec_ref(v___y_1519_);
lean_dec(v___y_1518_);
lean_dec_ref(v___y_1517_);
lean_dec(v___y_1516_);
return v_res_1524_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13(lean_object* v_00_u03b1_1525_, lean_object* v_ref_1526_, lean_object* v_msg_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_){
_start:
{
lean_object* v___x_1536_; 
v___x_1536_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13___redArg(v_ref_1526_, v_msg_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_);
return v___x_1536_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13___boxed(lean_object* v_00_u03b1_1537_, lean_object* v_ref_1538_, lean_object* v_msg_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_){
_start:
{
lean_object* v_res_1548_; 
v_res_1548_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13(v_00_u03b1_1537_, v_ref_1538_, v_msg_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_);
lean_dec(v___y_1546_);
lean_dec(v___y_1544_);
lean_dec_ref(v___y_1543_);
lean_dec(v___y_1542_);
lean_dec_ref(v___y_1541_);
lean_dec(v___y_1540_);
lean_dec(v_ref_1538_);
return v_res_1548_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15(lean_object* v_00_u03b1_1549_, lean_object* v_msg_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_){
_start:
{
lean_object* v___x_1559_; 
v___x_1559_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15___redArg(v_msg_1550_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_);
return v___x_1559_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15___boxed(lean_object* v_00_u03b1_1560_, lean_object* v_msg_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_){
_start:
{
lean_object* v_res_1570_; 
v_res_1570_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15(v_00_u03b1_1560_, v_msg_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
lean_dec(v___y_1566_);
lean_dec_ref(v___y_1565_);
lean_dec(v___y_1564_);
lean_dec_ref(v___y_1563_);
lean_dec(v___y_1562_);
return v_res_1570_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__31_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_12_(){
_start:
{
lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; 
v___x_1578_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__31___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_12_));
v___x_1579_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__26___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_12_));
v___x_1580_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_paramMatcher___boxed), 9, 0);
v___x_1581_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1578_, v___x_1579_, v___x_1580_);
return v___x_1581_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__31_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_12____boxed(lean_object* v_a_1582_){
_start:
{
lean_object* v_res_1583_; 
v_res_1583_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__31_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_12_();
return v_res_1583_;
}
}
static lean_object* _init_l_Lean_Elab_WF_paramMatcher___regBuiltin_Lean_Elab_WF_paramMatcher_declare__1___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_14_(void){
_start:
{
lean_object* v___x_1584_; lean_object* v___x_1585_; 
v___x_1584_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_paramMatcher___boxed), 9, 0);
v___x_1585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1585_, 0, v___x_1584_);
return v___x_1585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramMatcher___regBuiltin_Lean_Elab_WF_paramMatcher_declare__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_14_(){
_start:
{
lean_object* v___x_1587_; uint8_t v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; 
v___x_1587_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__31___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_12_));
v___x_1588_ = 1;
v___x_1589_ = lean_obj_once(&l_Lean_Elab_WF_paramMatcher___regBuiltin_Lean_Elab_WF_paramMatcher_declare__1___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_14_, &l_Lean_Elab_WF_paramMatcher___regBuiltin_Lean_Elab_WF_paramMatcher_declare__1___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_14__once, _init_l_Lean_Elab_WF_paramMatcher___regBuiltin_Lean_Elab_WF_paramMatcher_declare__1___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_14_);
v___x_1590_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1587_, v___x_1588_, v___x_1589_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramMatcher___regBuiltin_Lean_Elab_WF_paramMatcher_declare__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_14____boxed(lean_object* v_a_1591_){
_start:
{
lean_object* v_res_1592_; 
v_res_1592_ = l_Lean_Elab_WF_paramMatcher___regBuiltin_Lean_Elab_WF_paramMatcher_declare__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_14_();
return v_res_1592_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_anyLetValueIsWfParam(lean_object* v_e_1593_){
_start:
{
if (lean_obj_tag(v_e_1593_) == 8)
{
lean_object* v_value_1594_; lean_object* v_body_1595_; lean_object* v___x_1596_; 
v_value_1594_ = lean_ctor_get(v_e_1593_, 2);
v_body_1595_ = lean_ctor_get(v_e_1593_, 3);
v___x_1596_ = l_Lean_Elab_WF_isWfParam_x3f(v_value_1594_);
if (lean_obj_tag(v___x_1596_) == 0)
{
v_e_1593_ = v_body_1595_;
goto _start;
}
else
{
uint8_t v___x_1598_; 
lean_dec_ref(v___x_1596_);
v___x_1598_ = 1;
return v___x_1598_;
}
}
else
{
uint8_t v___x_1599_; 
v___x_1599_ = 0;
return v___x_1599_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_anyLetValueIsWfParam___boxed(lean_object* v_e_1600_){
_start:
{
uint8_t v_res_1601_; lean_object* v_r_1602_; 
v_res_1601_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_anyLetValueIsWfParam(v_e_1600_);
lean_dec_ref(v_e_1600_);
v_r_1602_ = lean_box(v_res_1601_);
return v_r_1602_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_numLetsWithValueNotIsWfParam(lean_object* v_e_1603_, lean_object* v_acc_1604_){
_start:
{
if (lean_obj_tag(v_e_1603_) == 8)
{
lean_object* v_value_1605_; lean_object* v_body_1606_; lean_object* v___x_1607_; 
v_value_1605_ = lean_ctor_get(v_e_1603_, 2);
v_body_1606_ = lean_ctor_get(v_e_1603_, 3);
v___x_1607_ = l_Lean_Elab_WF_isWfParam_x3f(v_value_1605_);
if (lean_obj_tag(v___x_1607_) == 0)
{
lean_object* v___x_1608_; lean_object* v___x_1609_; 
v___x_1608_ = lean_unsigned_to_nat(1u);
v___x_1609_ = lean_nat_add(v_acc_1604_, v___x_1608_);
lean_dec(v_acc_1604_);
v_e_1603_ = v_body_1606_;
v_acc_1604_ = v___x_1609_;
goto _start;
}
else
{
lean_dec_ref(v___x_1607_);
return v_acc_1604_;
}
}
else
{
return v_acc_1604_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_numLetsWithValueNotIsWfParam___boxed(lean_object* v_e_1611_, lean_object* v_acc_1612_){
_start:
{
lean_object* v_res_1613_; 
v_res_1613_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_numLetsWithValueNotIsWfParam(v_e_1611_, v_acc_1612_);
lean_dec_ref(v_e_1611_);
return v_res_1613_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__0(lean_object* v_msg_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_){
_start:
{
lean_object* v___f_1621_; lean_object* v___x_1335__overap_1622_; lean_object* v___x_1623_; 
v___f_1621_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__0___closed__0));
v___x_1335__overap_1622_ = lean_panic_fn(v___f_1621_, v_msg_1615_);
v___x_1623_ = lean_apply_5(v___x_1335__overap_1622_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, lean_box(0));
return v___x_1623_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__0___boxed(lean_object* v_msg_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_){
_start:
{
lean_object* v_res_1630_; 
v_res_1630_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__0(v_msg_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_);
return v_res_1630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg___lam__0(lean_object* v_k_1631_, lean_object* v_b_1632_, lean_object* v_c_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_){
_start:
{
lean_object* v___x_1639_; 
v___x_1639_ = lean_apply_7(v_k_1631_, v_b_1632_, v_c_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, lean_box(0));
return v___x_1639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg___lam__0___boxed(lean_object* v_k_1640_, lean_object* v_b_1641_, lean_object* v_c_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_){
_start:
{
lean_object* v_res_1648_; 
v_res_1648_ = l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg___lam__0(v_k_1640_, v_b_1641_, v_c_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_);
return v_res_1648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg(lean_object* v_e_1649_, lean_object* v_maxFVars_x3f_1650_, lean_object* v_k_1651_, uint8_t v_cleanupAnnotations_1652_, uint8_t v_preserveNondepLet_1653_, uint8_t v_nondepLetOnly_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_){
_start:
{
lean_object* v___f_1660_; uint8_t v___x_1661_; uint8_t v___x_1662_; lean_object* v___x_1663_; 
v___f_1660_ = lean_alloc_closure((void*)(l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1660_, 0, v_k_1651_);
v___x_1661_ = 0;
v___x_1662_ = 1;
v___x_1663_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_1649_, v___x_1661_, v___x_1662_, v_preserveNondepLet_1653_, v_nondepLetOnly_1654_, v_maxFVars_x3f_1650_, v___f_1660_, v_cleanupAnnotations_1652_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_);
if (lean_obj_tag(v___x_1663_) == 0)
{
lean_object* v_a_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1671_; 
v_a_1664_ = lean_ctor_get(v___x_1663_, 0);
v_isSharedCheck_1671_ = !lean_is_exclusive(v___x_1663_);
if (v_isSharedCheck_1671_ == 0)
{
v___x_1666_ = v___x_1663_;
v_isShared_1667_ = v_isSharedCheck_1671_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_a_1664_);
lean_dec(v___x_1663_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1671_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v___x_1669_; 
if (v_isShared_1667_ == 0)
{
v___x_1669_ = v___x_1666_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v_a_1664_);
v___x_1669_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
return v___x_1669_;
}
}
}
else
{
lean_object* v_a_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1679_; 
v_a_1672_ = lean_ctor_get(v___x_1663_, 0);
v_isSharedCheck_1679_ = !lean_is_exclusive(v___x_1663_);
if (v_isSharedCheck_1679_ == 0)
{
v___x_1674_ = v___x_1663_;
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_a_1672_);
lean_dec(v___x_1663_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1677_; 
if (v_isShared_1675_ == 0)
{
v___x_1677_ = v___x_1674_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v_a_1672_);
v___x_1677_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
return v___x_1677_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg___boxed(lean_object* v_e_1680_, lean_object* v_maxFVars_x3f_1681_, lean_object* v_k_1682_, lean_object* v_cleanupAnnotations_1683_, lean_object* v_preserveNondepLet_1684_, lean_object* v_nondepLetOnly_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1691_; uint8_t v_preserveNondepLet_boxed_1692_; uint8_t v_nondepLetOnly_boxed_1693_; lean_object* v_res_1694_; 
v_cleanupAnnotations_boxed_1691_ = lean_unbox(v_cleanupAnnotations_1683_);
v_preserveNondepLet_boxed_1692_ = lean_unbox(v_preserveNondepLet_1684_);
v_nondepLetOnly_boxed_1693_ = lean_unbox(v_nondepLetOnly_1685_);
v_res_1694_ = l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg(v_e_1680_, v_maxFVars_x3f_1681_, v_k_1682_, v_cleanupAnnotations_boxed_1691_, v_preserveNondepLet_boxed_1692_, v_nondepLetOnly_boxed_1693_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_);
lean_dec(v_maxFVars_x3f_1681_);
return v_res_1694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1(lean_object* v_00_u03b1_1695_, lean_object* v_e_1696_, lean_object* v_maxFVars_x3f_1697_, lean_object* v_k_1698_, uint8_t v_cleanupAnnotations_1699_, uint8_t v_preserveNondepLet_1700_, uint8_t v_nondepLetOnly_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_){
_start:
{
lean_object* v___x_1707_; 
v___x_1707_ = l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg(v_e_1696_, v_maxFVars_x3f_1697_, v_k_1698_, v_cleanupAnnotations_1699_, v_preserveNondepLet_1700_, v_nondepLetOnly_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
return v___x_1707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___boxed(lean_object* v_00_u03b1_1708_, lean_object* v_e_1709_, lean_object* v_maxFVars_x3f_1710_, lean_object* v_k_1711_, lean_object* v_cleanupAnnotations_1712_, lean_object* v_preserveNondepLet_1713_, lean_object* v_nondepLetOnly_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1720_; uint8_t v_preserveNondepLet_boxed_1721_; uint8_t v_nondepLetOnly_boxed_1722_; lean_object* v_res_1723_; 
v_cleanupAnnotations_boxed_1720_ = lean_unbox(v_cleanupAnnotations_1712_);
v_preserveNondepLet_boxed_1721_ = lean_unbox(v_preserveNondepLet_1713_);
v_nondepLetOnly_boxed_1722_ = lean_unbox(v_nondepLetOnly_1714_);
v_res_1723_ = l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1(v_00_u03b1_1708_, v_e_1709_, v_maxFVars_x3f_1710_, v_k_1711_, v_cleanupAnnotations_boxed_1720_, v_preserveNondepLet_boxed_1721_, v_nondepLetOnly_boxed_1722_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_);
lean_dec(v_maxFVars_x3f_1710_);
return v_res_1723_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__0(void){
_start:
{
lean_object* v___x_1724_; lean_object* v___x_1725_; 
v___x_1724_ = lean_unsigned_to_nat(0u);
v___x_1725_ = l_Lean_Expr_bvar___override(v___x_1724_);
return v___x_1725_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__4(void){
_start:
{
lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; 
v___x_1729_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__3));
v___x_1730_ = lean_unsigned_to_nat(6u);
v___x_1731_ = lean_unsigned_to_nat(138u);
v___x_1732_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__2));
v___x_1733_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__1));
v___x_1734_ = l_mkPanicMessageWithDecl(v___x_1733_, v___x_1732_, v___x_1731_, v___x_1730_, v___x_1729_);
return v___x_1734_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___lam__0___boxed(lean_object* v_xs_1735_, lean_object* v_b_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_){
_start:
{
lean_object* v_res_1742_; 
v_res_1742_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___lam__0(v_xs_1735_, v_b_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
lean_dec_ref(v_xs_1735_);
return v_res_1742_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet(lean_object* v_e_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_){
_start:
{
if (lean_obj_tag(v_e_1743_) == 8)
{
lean_object* v_declName_1749_; lean_object* v_type_1750_; lean_object* v_value_1751_; lean_object* v_body_1752_; uint8_t v_nondep_1753_; lean_object* v___x_1754_; 
v_declName_1749_ = lean_ctor_get(v_e_1743_, 0);
v_type_1750_ = lean_ctor_get(v_e_1743_, 1);
v_value_1751_ = lean_ctor_get(v_e_1743_, 2);
v_body_1752_ = lean_ctor_get(v_e_1743_, 3);
v_nondep_1753_ = lean_ctor_get_uint8(v_e_1743_, sizeof(void*)*4 + 8);
v___x_1754_ = l_Lean_Elab_WF_isWfParam_x3f(v_value_1751_);
if (lean_obj_tag(v___x_1754_) == 1)
{
lean_object* v_val_1755_; lean_object* v___x_1756_; 
v_val_1755_ = lean_ctor_get(v___x_1754_, 0);
lean_inc(v_val_1755_);
lean_dec_ref(v___x_1754_);
lean_inc(v_a_1747_);
lean_inc_ref(v_a_1746_);
lean_inc(v_a_1745_);
lean_inc_ref(v_a_1744_);
lean_inc_ref(v_type_1750_);
v___x_1756_ = l_Lean_Meta_isProp(v_type_1750_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_);
if (lean_obj_tag(v___x_1756_) == 0)
{
lean_object* v_a_1757_; uint8_t v___y_1759_; uint8_t v___x_1767_; 
v_a_1757_ = lean_ctor_get(v___x_1756_, 0);
lean_inc(v_a_1757_);
lean_dec_ref(v___x_1756_);
v___x_1767_ = lean_unbox(v_a_1757_);
lean_dec(v_a_1757_);
if (v___x_1767_ == 0)
{
lean_object* v___x_1768_; 
lean_inc(v_a_1747_);
lean_inc_ref(v_a_1746_);
lean_inc(v_a_1745_);
lean_inc_ref(v_a_1744_);
lean_inc_ref(v_type_1750_);
v___x_1768_ = l_Lean_Meta_getLevel(v_type_1750_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_);
if (lean_obj_tag(v___x_1768_) == 0)
{
lean_object* v_a_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; uint8_t v___y_1778_; size_t v___x_1787_; uint8_t v___x_1788_; 
v_a_1769_ = lean_ctor_get(v___x_1768_, 0);
lean_inc(v_a_1769_);
lean_dec_ref(v___x_1768_);
v___x_1770_ = ((lean_object*)(l_Lean_Elab_WF_isWfParam_x3f___closed__1));
v___x_1771_ = lean_box(0);
v___x_1772_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1772_, 0, v_a_1769_);
lean_ctor_set(v___x_1772_, 1, v___x_1771_);
v___x_1773_ = l_Lean_Expr_const___override(v___x_1770_, v___x_1772_);
v___x_1774_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__0, &l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__0);
lean_inc_ref(v_type_1750_);
v___x_1775_ = l_Lean_mkAppB(v___x_1773_, v_type_1750_, v___x_1774_);
v___x_1776_ = lean_expr_instantiate1(v_body_1752_, v___x_1775_);
lean_dec_ref(v___x_1775_);
v___x_1787_ = lean_ptr_addr(v_type_1750_);
v___x_1788_ = lean_usize_dec_eq(v___x_1787_, v___x_1787_);
if (v___x_1788_ == 0)
{
v___y_1778_ = v___x_1788_;
goto v___jp_1777_;
}
else
{
size_t v___x_1789_; size_t v___x_1790_; uint8_t v___x_1791_; 
v___x_1789_ = lean_ptr_addr(v_value_1751_);
v___x_1790_ = lean_ptr_addr(v_val_1755_);
v___x_1791_ = lean_usize_dec_eq(v___x_1789_, v___x_1790_);
v___y_1778_ = v___x_1791_;
goto v___jp_1777_;
}
v___jp_1777_:
{
if (v___y_1778_ == 0)
{
lean_object* v___x_1779_; 
lean_inc_ref(v_type_1750_);
lean_inc(v_declName_1749_);
lean_dec_ref(v_e_1743_);
v___x_1779_ = l_Lean_Expr_letE___override(v_declName_1749_, v_type_1750_, v_val_1755_, v___x_1776_, v_nondep_1753_);
v_e_1743_ = v___x_1779_;
goto _start;
}
else
{
size_t v___x_1781_; size_t v___x_1782_; uint8_t v___x_1783_; 
v___x_1781_ = lean_ptr_addr(v_body_1752_);
v___x_1782_ = lean_ptr_addr(v___x_1776_);
v___x_1783_ = lean_usize_dec_eq(v___x_1781_, v___x_1782_);
if (v___x_1783_ == 0)
{
lean_object* v___x_1784_; 
lean_inc_ref(v_type_1750_);
lean_inc(v_declName_1749_);
lean_dec_ref(v_e_1743_);
v___x_1784_ = l_Lean_Expr_letE___override(v_declName_1749_, v_type_1750_, v_val_1755_, v___x_1776_, v_nondep_1753_);
v_e_1743_ = v___x_1784_;
goto _start;
}
else
{
lean_dec_ref(v___x_1776_);
lean_dec(v_val_1755_);
goto _start;
}
}
}
}
else
{
lean_object* v_a_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1799_; 
lean_dec(v_val_1755_);
lean_dec_ref(v_e_1743_);
lean_dec(v_a_1747_);
lean_dec_ref(v_a_1746_);
lean_dec(v_a_1745_);
lean_dec_ref(v_a_1744_);
v_a_1792_ = lean_ctor_get(v___x_1768_, 0);
v_isSharedCheck_1799_ = !lean_is_exclusive(v___x_1768_);
if (v_isSharedCheck_1799_ == 0)
{
v___x_1794_ = v___x_1768_;
v_isShared_1795_ = v_isSharedCheck_1799_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_a_1792_);
lean_dec(v___x_1768_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1799_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
lean_object* v___x_1797_; 
if (v_isShared_1795_ == 0)
{
v___x_1797_ = v___x_1794_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v_a_1792_);
v___x_1797_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
return v___x_1797_;
}
}
}
}
else
{
size_t v___x_1800_; uint8_t v___x_1801_; 
v___x_1800_ = lean_ptr_addr(v_type_1750_);
v___x_1801_ = lean_usize_dec_eq(v___x_1800_, v___x_1800_);
if (v___x_1801_ == 0)
{
v___y_1759_ = v___x_1801_;
goto v___jp_1758_;
}
else
{
size_t v___x_1802_; size_t v___x_1803_; uint8_t v___x_1804_; 
v___x_1802_ = lean_ptr_addr(v_value_1751_);
v___x_1803_ = lean_ptr_addr(v_val_1755_);
v___x_1804_ = lean_usize_dec_eq(v___x_1802_, v___x_1803_);
v___y_1759_ = v___x_1804_;
goto v___jp_1758_;
}
}
v___jp_1758_:
{
if (v___y_1759_ == 0)
{
lean_object* v___x_1760_; 
lean_inc_ref(v_body_1752_);
lean_inc_ref(v_type_1750_);
lean_inc(v_declName_1749_);
lean_dec_ref(v_e_1743_);
v___x_1760_ = l_Lean_Expr_letE___override(v_declName_1749_, v_type_1750_, v_val_1755_, v_body_1752_, v_nondep_1753_);
v_e_1743_ = v___x_1760_;
goto _start;
}
else
{
size_t v___x_1762_; uint8_t v___x_1763_; 
v___x_1762_ = lean_ptr_addr(v_body_1752_);
v___x_1763_ = lean_usize_dec_eq(v___x_1762_, v___x_1762_);
if (v___x_1763_ == 0)
{
lean_object* v___x_1764_; 
lean_inc_ref(v_body_1752_);
lean_inc_ref(v_type_1750_);
lean_inc(v_declName_1749_);
lean_dec_ref(v_e_1743_);
v___x_1764_ = l_Lean_Expr_letE___override(v_declName_1749_, v_type_1750_, v_val_1755_, v_body_1752_, v_nondep_1753_);
v_e_1743_ = v___x_1764_;
goto _start;
}
else
{
lean_dec(v_val_1755_);
goto _start;
}
}
}
}
else
{
lean_object* v_a_1805_; lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1812_; 
lean_dec(v_val_1755_);
lean_dec_ref(v_e_1743_);
lean_dec(v_a_1747_);
lean_dec_ref(v_a_1746_);
lean_dec(v_a_1745_);
lean_dec_ref(v_a_1744_);
v_a_1805_ = lean_ctor_get(v___x_1756_, 0);
v_isSharedCheck_1812_ = !lean_is_exclusive(v___x_1756_);
if (v_isSharedCheck_1812_ == 0)
{
v___x_1807_ = v___x_1756_;
v_isShared_1808_ = v_isSharedCheck_1812_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_a_1805_);
lean_dec(v___x_1756_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1812_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
lean_object* v___x_1810_; 
if (v_isShared_1808_ == 0)
{
v___x_1810_ = v___x_1807_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v_a_1805_);
v___x_1810_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
return v___x_1810_;
}
}
}
}
else
{
lean_object* v___x_1813_; lean_object* v_num_1814_; uint8_t v___x_1815_; 
lean_dec(v___x_1754_);
v___x_1813_ = lean_unsigned_to_nat(0u);
v_num_1814_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_numLetsWithValueNotIsWfParam(v_e_1743_, v___x_1813_);
v___x_1815_ = lean_nat_dec_lt(v___x_1813_, v_num_1814_);
if (v___x_1815_ == 0)
{
lean_object* v___x_1816_; lean_object* v___x_1817_; 
lean_dec(v_num_1814_);
lean_dec_ref(v_e_1743_);
v___x_1816_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__4, &l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__4);
v___x_1817_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__0(v___x_1816_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_);
return v___x_1817_;
}
else
{
lean_object* v___f_1818_; lean_object* v___x_1819_; uint8_t v___x_1820_; lean_object* v___x_1821_; 
v___f_1818_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___lam__0___boxed), 7, 0);
v___x_1819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1819_, 0, v_num_1814_);
v___x_1820_ = 0;
v___x_1821_ = l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg(v_e_1743_, v___x_1819_, v___f_1818_, v___x_1820_, v___x_1815_, v___x_1820_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_);
lean_dec_ref(v___x_1819_);
return v___x_1821_;
}
}
}
else
{
lean_object* v___x_1822_; 
lean_dec(v_a_1747_);
lean_dec_ref(v_a_1746_);
lean_dec(v_a_1745_);
lean_dec_ref(v_a_1744_);
v___x_1822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1822_, 0, v_e_1743_);
return v___x_1822_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___lam__0(lean_object* v_xs_1823_, lean_object* v_b_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_){
_start:
{
lean_object* v___x_1830_; 
lean_inc(v___y_1828_);
lean_inc_ref(v___y_1827_);
lean_inc(v___y_1826_);
lean_inc_ref(v___y_1825_);
v___x_1830_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet(v_b_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_);
if (lean_obj_tag(v___x_1830_) == 0)
{
lean_object* v_a_1831_; uint8_t v___x_1832_; uint8_t v___x_1833_; lean_object* v___x_1834_; 
v_a_1831_ = lean_ctor_get(v___x_1830_, 0);
lean_inc(v_a_1831_);
lean_dec_ref(v___x_1830_);
v___x_1832_ = 0;
v___x_1833_ = 1;
v___x_1834_ = l_Lean_Meta_mkLetFVars(v_xs_1823_, v_a_1831_, v___x_1832_, v___x_1832_, v___x_1833_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_);
lean_dec(v___y_1828_);
lean_dec_ref(v___y_1827_);
lean_dec(v___y_1826_);
lean_dec_ref(v___y_1825_);
return v___x_1834_;
}
else
{
lean_dec(v___y_1828_);
lean_dec_ref(v___y_1827_);
lean_dec(v___y_1826_);
lean_dec_ref(v___y_1825_);
return v___x_1830_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___boxed(lean_object* v_e_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_){
_start:
{
lean_object* v_res_1841_; 
v_res_1841_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet(v_e_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_);
return v_res_1841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramLet___redArg(lean_object* v_e_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_){
_start:
{
uint8_t v___y_1849_; uint8_t v___x_1871_; 
v___x_1871_ = l_Lean_Expr_isLet(v_e_1842_);
if (v___x_1871_ == 0)
{
uint8_t v___x_1872_; 
v___x_1872_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_anyLetValueIsWfParam(v_e_1842_);
v___y_1849_ = v___x_1872_;
goto v___jp_1848_;
}
else
{
v___y_1849_ = v___x_1871_;
goto v___jp_1848_;
}
v___jp_1848_:
{
if (v___y_1849_ == 0)
{
lean_object* v___x_1850_; lean_object* v___x_1851_; 
lean_dec(v_a_1846_);
lean_dec_ref(v_a_1845_);
lean_dec(v_a_1844_);
lean_dec_ref(v_a_1843_);
lean_dec_ref(v_e_1842_);
v___x_1850_ = ((lean_object*)(l_Lean_Elab_WF_paramProj___closed__0));
v___x_1851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1850_);
return v___x_1851_;
}
else
{
lean_object* v___x_1852_; 
v___x_1852_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet(v_e_1842_, v_a_1843_, v_a_1844_, v_a_1845_, v_a_1846_);
if (lean_obj_tag(v___x_1852_) == 0)
{
lean_object* v_a_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1862_; 
v_a_1853_ = lean_ctor_get(v___x_1852_, 0);
v_isSharedCheck_1862_ = !lean_is_exclusive(v___x_1852_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1855_ = v___x_1852_;
v_isShared_1856_ = v_isSharedCheck_1862_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_a_1853_);
lean_dec(v___x_1852_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1862_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1860_; 
v___x_1857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1857_, 0, v_a_1853_);
v___x_1858_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1858_, 0, v___x_1857_);
if (v_isShared_1856_ == 0)
{
lean_ctor_set(v___x_1855_, 0, v___x_1858_);
v___x_1860_ = v___x_1855_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v___x_1858_);
v___x_1860_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
return v___x_1860_;
}
}
}
else
{
lean_object* v_a_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1870_; 
v_a_1863_ = lean_ctor_get(v___x_1852_, 0);
v_isSharedCheck_1870_ = !lean_is_exclusive(v___x_1852_);
if (v_isSharedCheck_1870_ == 0)
{
v___x_1865_ = v___x_1852_;
v_isShared_1866_ = v_isSharedCheck_1870_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_a_1863_);
lean_dec(v___x_1852_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1870_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
lean_object* v___x_1868_; 
if (v_isShared_1866_ == 0)
{
v___x_1868_ = v___x_1865_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v_a_1863_);
v___x_1868_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
return v___x_1868_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramLet___redArg___boxed(lean_object* v_e_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_){
_start:
{
lean_object* v_res_1879_; 
v_res_1879_ = l_Lean_Elab_WF_paramLet___redArg(v_e_1873_, v_a_1874_, v_a_1875_, v_a_1876_, v_a_1877_);
return v_res_1879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramLet(lean_object* v_e_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_){
_start:
{
lean_object* v___x_1889_; 
v___x_1889_ = l_Lean_Elab_WF_paramLet___redArg(v_e_1880_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_);
return v___x_1889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramLet___boxed(lean_object* v_e_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_){
_start:
{
lean_object* v_res_1899_; 
v_res_1899_ = l_Lean_Elab_WF_paramLet(v_e_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_);
lean_dec(v_a_1893_);
lean_dec_ref(v_a_1892_);
lean_dec(v_a_1891_);
return v_res_1899_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__52_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12_(){
_start:
{
lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; 
v___x_1907_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__52___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12_));
v___x_1908_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__26___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_12_));
v___x_1909_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_paramLet___boxed), 9, 0);
v___x_1910_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1907_, v___x_1908_, v___x_1909_);
return v___x_1910_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__52_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12____boxed(lean_object* v_a_1911_){
_start:
{
lean_object* v_res_1912_; 
v_res_1912_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__52_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12_();
return v_res_1912_;
}
}
static lean_object* _init_l_Lean_Elab_WF_paramLet___regBuiltin_Lean_Elab_WF_paramLet_declare__1___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_14_(void){
_start:
{
lean_object* v___x_1913_; lean_object* v___x_1914_; 
v___x_1913_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_paramLet___boxed), 9, 0);
v___x_1914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1914_, 0, v___x_1913_);
return v___x_1914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramLet___regBuiltin_Lean_Elab_WF_paramLet_declare__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_14_(){
_start:
{
lean_object* v___x_1916_; uint8_t v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; 
v___x_1916_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__52___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12_));
v___x_1917_ = 1;
v___x_1918_ = lean_obj_once(&l_Lean_Elab_WF_paramLet___regBuiltin_Lean_Elab_WF_paramLet_declare__1___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_14_, &l_Lean_Elab_WF_paramLet___regBuiltin_Lean_Elab_WF_paramLet_declare__1___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_14__once, _init_l_Lean_Elab_WF_paramLet___regBuiltin_Lean_Elab_WF_paramLet_declare__1___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_14_);
v___x_1919_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1916_, v___x_1917_, v___x_1918_);
return v___x_1919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramLet___regBuiltin_Lean_Elab_WF_paramLet_declare__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_14____boxed(lean_object* v_a_1920_){
_start:
{
lean_object* v_res_1921_; 
v_res_1921_ = l_Lean_Elab_WF_paramLet___regBuiltin_Lean_Elab_WF_paramLet_declare__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_14_();
return v_res_1921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__0___redArg(lean_object* v_lctx_1922_, lean_object* v_x_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_){
_start:
{
lean_object* v_keyedConfig_1929_; uint8_t v_trackZetaDelta_1930_; lean_object* v_zetaDeltaSet_1931_; lean_object* v_localInstances_1932_; lean_object* v_defEqCtx_x3f_1933_; lean_object* v_synthPendingDepth_1934_; lean_object* v_canUnfold_x3f_1935_; uint8_t v_univApprox_1936_; uint8_t v_inTypeClassResolution_1937_; uint8_t v_cacheInferType_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1946_; 
v_keyedConfig_1929_ = lean_ctor_get(v___y_1924_, 0);
v_trackZetaDelta_1930_ = lean_ctor_get_uint8(v___y_1924_, sizeof(void*)*7);
v_zetaDeltaSet_1931_ = lean_ctor_get(v___y_1924_, 1);
v_localInstances_1932_ = lean_ctor_get(v___y_1924_, 3);
v_defEqCtx_x3f_1933_ = lean_ctor_get(v___y_1924_, 4);
v_synthPendingDepth_1934_ = lean_ctor_get(v___y_1924_, 5);
v_canUnfold_x3f_1935_ = lean_ctor_get(v___y_1924_, 6);
v_univApprox_1936_ = lean_ctor_get_uint8(v___y_1924_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1937_ = lean_ctor_get_uint8(v___y_1924_, sizeof(void*)*7 + 2);
v_cacheInferType_1938_ = lean_ctor_get_uint8(v___y_1924_, sizeof(void*)*7 + 3);
v_isSharedCheck_1946_ = !lean_is_exclusive(v___y_1924_);
if (v_isSharedCheck_1946_ == 0)
{
lean_object* v_unused_1947_; 
v_unused_1947_ = lean_ctor_get(v___y_1924_, 2);
lean_dec(v_unused_1947_);
v___x_1940_ = v___y_1924_;
v_isShared_1941_ = v_isSharedCheck_1946_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_canUnfold_x3f_1935_);
lean_inc(v_synthPendingDepth_1934_);
lean_inc(v_defEqCtx_x3f_1933_);
lean_inc(v_localInstances_1932_);
lean_inc(v_zetaDeltaSet_1931_);
lean_inc(v_keyedConfig_1929_);
lean_dec(v___y_1924_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1946_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v___x_1943_; 
if (v_isShared_1941_ == 0)
{
lean_ctor_set(v___x_1940_, 2, v_lctx_1922_);
v___x_1943_ = v___x_1940_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v_keyedConfig_1929_);
lean_ctor_set(v_reuseFailAlloc_1945_, 1, v_zetaDeltaSet_1931_);
lean_ctor_set(v_reuseFailAlloc_1945_, 2, v_lctx_1922_);
lean_ctor_set(v_reuseFailAlloc_1945_, 3, v_localInstances_1932_);
lean_ctor_set(v_reuseFailAlloc_1945_, 4, v_defEqCtx_x3f_1933_);
lean_ctor_set(v_reuseFailAlloc_1945_, 5, v_synthPendingDepth_1934_);
lean_ctor_set(v_reuseFailAlloc_1945_, 6, v_canUnfold_x3f_1935_);
lean_ctor_set_uint8(v_reuseFailAlloc_1945_, sizeof(void*)*7, v_trackZetaDelta_1930_);
lean_ctor_set_uint8(v_reuseFailAlloc_1945_, sizeof(void*)*7 + 1, v_univApprox_1936_);
lean_ctor_set_uint8(v_reuseFailAlloc_1945_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1937_);
lean_ctor_set_uint8(v_reuseFailAlloc_1945_, sizeof(void*)*7 + 3, v_cacheInferType_1938_);
v___x_1943_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
lean_object* v___x_1944_; 
v___x_1944_ = lean_apply_5(v_x_1923_, v___x_1943_, v___y_1925_, v___y_1926_, v___y_1927_, lean_box(0));
return v___x_1944_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__0___redArg___boxed(lean_object* v_lctx_1948_, lean_object* v_x_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_){
_start:
{
lean_object* v_res_1955_; 
v_res_1955_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__0___redArg(v_lctx_1948_, v_x_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_);
return v_res_1955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__0(lean_object* v_00_u03b1_1956_, lean_object* v_lctx_1957_, lean_object* v_x_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_){
_start:
{
lean_object* v___x_1964_; 
v___x_1964_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__0___redArg(v_lctx_1957_, v_x_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_);
return v___x_1964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__0___boxed(lean_object* v_00_u03b1_1965_, lean_object* v_lctx_1966_, lean_object* v_x_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_){
_start:
{
lean_object* v_res_1973_; 
v_res_1973_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__0(v_00_u03b1_1965_, v_lctx_1966_, v_x_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_);
return v_res_1973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__2___redArg(lean_object* v_e_1974_, lean_object* v_k_1975_, uint8_t v_cleanupAnnotations_1976_, uint8_t v_preserveNondepLet_1977_, uint8_t v_nondepLetOnly_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_){
_start:
{
lean_object* v___f_1984_; uint8_t v___x_1985_; uint8_t v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; 
v___f_1984_ = lean_alloc_closure((void*)(l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1984_, 0, v_k_1975_);
v___x_1985_ = 0;
v___x_1986_ = 1;
v___x_1987_ = lean_box(0);
v___x_1988_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_1974_, v___x_1985_, v___x_1986_, v_preserveNondepLet_1977_, v_nondepLetOnly_1978_, v___x_1987_, v___f_1984_, v_cleanupAnnotations_1976_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_);
if (lean_obj_tag(v___x_1988_) == 0)
{
lean_object* v_a_1989_; lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_1996_; 
v_a_1989_ = lean_ctor_get(v___x_1988_, 0);
v_isSharedCheck_1996_ = !lean_is_exclusive(v___x_1988_);
if (v_isSharedCheck_1996_ == 0)
{
v___x_1991_ = v___x_1988_;
v_isShared_1992_ = v_isSharedCheck_1996_;
goto v_resetjp_1990_;
}
else
{
lean_inc(v_a_1989_);
lean_dec(v___x_1988_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_1996_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
lean_object* v___x_1994_; 
if (v_isShared_1992_ == 0)
{
v___x_1994_ = v___x_1991_;
goto v_reusejp_1993_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v_a_1989_);
v___x_1994_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1993_;
}
v_reusejp_1993_:
{
return v___x_1994_;
}
}
}
else
{
lean_object* v_a_1997_; lean_object* v___x_1999_; uint8_t v_isShared_2000_; uint8_t v_isSharedCheck_2004_; 
v_a_1997_ = lean_ctor_get(v___x_1988_, 0);
v_isSharedCheck_2004_ = !lean_is_exclusive(v___x_1988_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1999_ = v___x_1988_;
v_isShared_2000_ = v_isSharedCheck_2004_;
goto v_resetjp_1998_;
}
else
{
lean_inc(v_a_1997_);
lean_dec(v___x_1988_);
v___x_1999_ = lean_box(0);
v_isShared_2000_ = v_isSharedCheck_2004_;
goto v_resetjp_1998_;
}
v_resetjp_1998_:
{
lean_object* v___x_2002_; 
if (v_isShared_2000_ == 0)
{
v___x_2002_ = v___x_1999_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v_a_1997_);
v___x_2002_ = v_reuseFailAlloc_2003_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
return v___x_2002_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__2___redArg___boxed(lean_object* v_e_2005_, lean_object* v_k_2006_, lean_object* v_cleanupAnnotations_2007_, lean_object* v_preserveNondepLet_2008_, lean_object* v_nondepLetOnly_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2015_; uint8_t v_preserveNondepLet_boxed_2016_; uint8_t v_nondepLetOnly_boxed_2017_; lean_object* v_res_2018_; 
v_cleanupAnnotations_boxed_2015_ = lean_unbox(v_cleanupAnnotations_2007_);
v_preserveNondepLet_boxed_2016_ = lean_unbox(v_preserveNondepLet_2008_);
v_nondepLetOnly_boxed_2017_ = lean_unbox(v_nondepLetOnly_2009_);
v_res_2018_ = l_Lean_Meta_letTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__2___redArg(v_e_2005_, v_k_2006_, v_cleanupAnnotations_boxed_2015_, v_preserveNondepLet_boxed_2016_, v_nondepLetOnly_boxed_2017_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_);
return v_res_2018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__2(lean_object* v_00_u03b1_2019_, lean_object* v_e_2020_, lean_object* v_k_2021_, uint8_t v_cleanupAnnotations_2022_, uint8_t v_preserveNondepLet_2023_, uint8_t v_nondepLetOnly_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_){
_start:
{
lean_object* v___x_2030_; 
v___x_2030_ = l_Lean_Meta_letTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__2___redArg(v_e_2020_, v_k_2021_, v_cleanupAnnotations_2022_, v_preserveNondepLet_2023_, v_nondepLetOnly_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_);
return v___x_2030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__2___boxed(lean_object* v_00_u03b1_2031_, lean_object* v_e_2032_, lean_object* v_k_2033_, lean_object* v_cleanupAnnotations_2034_, lean_object* v_preserveNondepLet_2035_, lean_object* v_nondepLetOnly_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2042_; uint8_t v_preserveNondepLet_boxed_2043_; uint8_t v_nondepLetOnly_boxed_2044_; lean_object* v_res_2045_; 
v_cleanupAnnotations_boxed_2042_ = lean_unbox(v_cleanupAnnotations_2034_);
v_preserveNondepLet_boxed_2043_ = lean_unbox(v_preserveNondepLet_2035_);
v_nondepLetOnly_boxed_2044_ = lean_unbox(v_nondepLetOnly_2036_);
v_res_2045_ = l_Lean_Meta_letTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__2(v_00_u03b1_2031_, v_e_2032_, v_k_2033_, v_cleanupAnnotations_boxed_2042_, v_preserveNondepLet_boxed_2043_, v_nondepLetOnly_boxed_2044_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_);
return v_res_2045_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__0(lean_object* v_e_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_){
_start:
{
lean_object* v___x_2052_; lean_object* v___x_2053_; 
v___x_2052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2052_, 0, v_e_2046_);
v___x_2053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2053_, 0, v___x_2052_);
return v___x_2053_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__0___boxed(lean_object* v_e_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_){
_start:
{
lean_object* v_res_2060_; 
v_res_2060_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__0(v_e_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_);
lean_dec(v___y_2058_);
lean_dec_ref(v___y_2057_);
lean_dec(v___y_2056_);
lean_dec_ref(v___y_2055_);
return v_res_2060_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__1(lean_object* v_as_2061_, size_t v_i_2062_, size_t v_stop_2063_, lean_object* v_b_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_){
_start:
{
uint8_t v___x_2070_; 
v___x_2070_ = lean_usize_dec_eq(v_i_2062_, v_stop_2063_);
if (v___x_2070_ == 0)
{
lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; 
v___x_2071_ = lean_array_uget_borrowed(v_as_2061_, v_i_2062_);
v___x_2072_ = l_Lean_Expr_fvarId_x21(v___x_2071_);
lean_inc_ref(v___y_2065_);
v___x_2073_ = l_Lean_FVarId_getDecl___redArg(v___x_2072_, v___y_2065_, v___y_2067_, v___y_2068_);
if (lean_obj_tag(v___x_2073_) == 0)
{
lean_object* v_a_2074_; uint8_t v_a_2076_; uint8_t v___x_2082_; 
v_a_2074_ = lean_ctor_get(v___x_2073_, 0);
lean_inc(v_a_2074_);
lean_dec_ref(v___x_2073_);
v___x_2082_ = l_Lean_LocalDecl_isNondep(v_a_2074_);
if (v___x_2082_ == 0)
{
v_a_2076_ = v___x_2082_;
goto v___jp_2075_;
}
else
{
lean_object* v___x_2083_; lean_object* v___x_2084_; 
v___x_2083_ = l_Lean_LocalDecl_type(v_a_2074_);
lean_inc(v___y_2068_);
lean_inc_ref(v___y_2067_);
lean_inc(v___y_2066_);
lean_inc_ref(v___y_2065_);
v___x_2084_ = l_Lean_Meta_isProp(v___x_2083_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_);
if (lean_obj_tag(v___x_2084_) == 0)
{
lean_object* v_a_2085_; uint8_t v___x_2086_; 
v_a_2085_ = lean_ctor_get(v___x_2084_, 0);
lean_inc(v_a_2085_);
lean_dec_ref(v___x_2084_);
v___x_2086_ = lean_unbox(v_a_2085_);
lean_dec(v_a_2085_);
v_a_2076_ = v___x_2086_;
goto v___jp_2075_;
}
else
{
lean_object* v_a_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2094_; 
lean_dec(v_a_2074_);
lean_dec(v___y_2068_);
lean_dec_ref(v___y_2067_);
lean_dec(v___y_2066_);
lean_dec_ref(v___y_2065_);
lean_dec_ref(v_b_2064_);
v_a_2087_ = lean_ctor_get(v___x_2084_, 0);
v_isSharedCheck_2094_ = !lean_is_exclusive(v___x_2084_);
if (v_isSharedCheck_2094_ == 0)
{
v___x_2089_ = v___x_2084_;
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_a_2087_);
lean_dec(v___x_2084_);
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
v___jp_2075_:
{
lean_object* v___x_2077_; lean_object* v___x_2078_; size_t v___x_2079_; size_t v___x_2080_; 
v___x_2077_ = l_Lean_LocalDecl_setNondep(v_a_2074_, v_a_2076_);
v___x_2078_ = l_Lean_LocalContext_addDecl(v_b_2064_, v___x_2077_);
v___x_2079_ = ((size_t)1ULL);
v___x_2080_ = lean_usize_add(v_i_2062_, v___x_2079_);
v_i_2062_ = v___x_2080_;
v_b_2064_ = v___x_2078_;
goto _start;
}
}
else
{
lean_object* v_a_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2102_; 
lean_dec(v___y_2068_);
lean_dec_ref(v___y_2067_);
lean_dec(v___y_2066_);
lean_dec_ref(v___y_2065_);
lean_dec_ref(v_b_2064_);
v_a_2095_ = lean_ctor_get(v___x_2073_, 0);
v_isSharedCheck_2102_ = !lean_is_exclusive(v___x_2073_);
if (v_isSharedCheck_2102_ == 0)
{
v___x_2097_ = v___x_2073_;
v_isShared_2098_ = v_isSharedCheck_2102_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_a_2095_);
lean_dec(v___x_2073_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2102_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2100_; 
if (v_isShared_2098_ == 0)
{
v___x_2100_ = v___x_2097_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v_a_2095_);
v___x_2100_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
return v___x_2100_;
}
}
}
}
else
{
lean_object* v___x_2103_; 
lean_dec(v___y_2068_);
lean_dec_ref(v___y_2067_);
lean_dec(v___y_2066_);
lean_dec_ref(v___y_2065_);
v___x_2103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2103_, 0, v_b_2064_);
return v___x_2103_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__1___boxed(lean_object* v_as_2104_, lean_object* v_i_2105_, lean_object* v_stop_2106_, lean_object* v_b_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_){
_start:
{
size_t v_i_boxed_2113_; size_t v_stop_boxed_2114_; lean_object* v_res_2115_; 
v_i_boxed_2113_ = lean_unbox_usize(v_i_2105_);
lean_dec(v_i_2105_);
v_stop_boxed_2114_ = lean_unbox_usize(v_stop_2106_);
lean_dec(v_stop_2106_);
v_res_2115_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__1(v_as_2104_, v_i_boxed_2113_, v_stop_boxed_2114_, v_b_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_);
lean_dec_ref(v_as_2104_);
return v_res_2115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__1(uint8_t v_a_2116_, lean_object* v_lctx_2117_, lean_object* v_xs_2118_, lean_object* v_b_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_){
_start:
{
lean_object* v_a_2126_; lean_object* v___y_2134_; lean_object* v___x_2144_; lean_object* v___x_2145_; uint8_t v___x_2146_; 
v___x_2144_ = lean_unsigned_to_nat(0u);
v___x_2145_ = lean_array_get_size(v_xs_2118_);
v___x_2146_ = lean_nat_dec_lt(v___x_2144_, v___x_2145_);
if (v___x_2146_ == 0)
{
v_a_2126_ = v_lctx_2117_;
goto v___jp_2125_;
}
else
{
uint8_t v___x_2147_; 
v___x_2147_ = lean_nat_dec_le(v___x_2145_, v___x_2145_);
if (v___x_2147_ == 0)
{
if (v___x_2146_ == 0)
{
v_a_2126_ = v_lctx_2117_;
goto v___jp_2125_;
}
else
{
size_t v___x_2148_; size_t v___x_2149_; lean_object* v___x_2150_; 
v___x_2148_ = ((size_t)0ULL);
v___x_2149_ = lean_usize_of_nat(v___x_2145_);
lean_inc(v___y_2123_);
lean_inc_ref(v___y_2122_);
lean_inc(v___y_2121_);
lean_inc_ref(v___y_2120_);
v___x_2150_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__1(v_xs_2118_, v___x_2148_, v___x_2149_, v_lctx_2117_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_);
v___y_2134_ = v___x_2150_;
goto v___jp_2133_;
}
}
else
{
size_t v___x_2151_; size_t v___x_2152_; lean_object* v___x_2153_; 
v___x_2151_ = ((size_t)0ULL);
v___x_2152_ = lean_usize_of_nat(v___x_2145_);
lean_inc(v___y_2123_);
lean_inc_ref(v___y_2122_);
lean_inc(v___y_2121_);
lean_inc_ref(v___y_2120_);
v___x_2153_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__1(v_xs_2118_, v___x_2151_, v___x_2152_, v_lctx_2117_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_);
v___y_2134_ = v___x_2153_;
goto v___jp_2133_;
}
}
v___jp_2125_:
{
uint8_t v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; 
v___x_2127_ = 1;
v___x_2128_ = lean_box(v_a_2116_);
v___x_2129_ = lean_box(v_a_2116_);
v___x_2130_ = lean_box(v___x_2127_);
v___x_2131_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLetFVars___boxed), 10, 5);
lean_closure_set(v___x_2131_, 0, v_xs_2118_);
lean_closure_set(v___x_2131_, 1, v_b_2119_);
lean_closure_set(v___x_2131_, 2, v___x_2128_);
lean_closure_set(v___x_2131_, 3, v___x_2129_);
lean_closure_set(v___x_2131_, 4, v___x_2130_);
v___x_2132_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__0___redArg(v_a_2126_, v___x_2131_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_);
return v___x_2132_;
}
v___jp_2133_:
{
if (lean_obj_tag(v___y_2134_) == 0)
{
lean_object* v_a_2135_; 
v_a_2135_ = lean_ctor_get(v___y_2134_, 0);
lean_inc(v_a_2135_);
lean_dec_ref(v___y_2134_);
v_a_2126_ = v_a_2135_;
goto v___jp_2125_;
}
else
{
lean_object* v_a_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2143_; 
lean_dec(v___y_2123_);
lean_dec_ref(v___y_2122_);
lean_dec(v___y_2121_);
lean_dec_ref(v___y_2120_);
lean_dec_ref(v_b_2119_);
lean_dec_ref(v_xs_2118_);
v_a_2136_ = lean_ctor_get(v___y_2134_, 0);
v_isSharedCheck_2143_ = !lean_is_exclusive(v___y_2134_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2138_ = v___y_2134_;
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_a_2136_);
lean_dec(v___y_2134_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v___x_2141_; 
if (v_isShared_2139_ == 0)
{
v___x_2141_ = v___x_2138_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v_a_2136_);
v___x_2141_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
return v___x_2141_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__1___boxed(lean_object* v_a_2154_, lean_object* v_lctx_2155_, lean_object* v_xs_2156_, lean_object* v_b_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_){
_start:
{
uint8_t v_a_11276__boxed_2163_; lean_object* v_res_2164_; 
v_a_11276__boxed_2163_ = lean_unbox(v_a_2154_);
v_res_2164_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__1(v_a_11276__boxed_2163_, v_lctx_2155_, v_xs_2156_, v_b_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_);
return v_res_2164_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__2(lean_object* v_e_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_){
_start:
{
lean_object* v___x_2171_; 
lean_inc(v___y_2169_);
lean_inc_ref(v___y_2168_);
lean_inc(v___y_2167_);
lean_inc_ref(v___y_2166_);
lean_inc_ref(v_e_2165_);
v___x_2171_ = l_Lean_Meta_isProof(v_e_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_);
if (lean_obj_tag(v___x_2171_) == 0)
{
lean_object* v_a_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2209_; 
v_a_2172_ = lean_ctor_get(v___x_2171_, 0);
v_isSharedCheck_2209_ = !lean_is_exclusive(v___x_2171_);
if (v_isSharedCheck_2209_ == 0)
{
v___x_2174_ = v___x_2171_;
v_isShared_2175_ = v_isSharedCheck_2209_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_a_2172_);
lean_dec(v___x_2171_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2209_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
uint8_t v___x_2176_; 
v___x_2176_ = lean_unbox(v_a_2172_);
if (v___x_2176_ == 0)
{
uint8_t v___x_2177_; 
v___x_2177_ = l_Lean_Expr_isLet(v_e_2165_);
if (v___x_2177_ == 0)
{
lean_object* v___x_2178_; lean_object* v___x_2180_; 
lean_dec(v_a_2172_);
lean_dec(v___y_2169_);
lean_dec_ref(v___y_2168_);
lean_dec(v___y_2167_);
lean_dec_ref(v___y_2166_);
lean_dec_ref(v_e_2165_);
v___x_2178_ = ((lean_object*)(l_Lean_Elab_WF_paramProj___closed__0));
if (v_isShared_2175_ == 0)
{
lean_ctor_set(v___x_2174_, 0, v___x_2178_);
v___x_2180_ = v___x_2174_;
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
else
{
lean_object* v_lctx_2182_; lean_object* v___f_2183_; uint8_t v___x_2184_; uint8_t v___x_2185_; lean_object* v___x_2186_; 
lean_del_object(v___x_2174_);
v_lctx_2182_ = lean_ctor_get(v___y_2166_, 2);
lean_inc_ref(v_lctx_2182_);
lean_inc(v_a_2172_);
v___f_2183_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__1___boxed), 9, 2);
lean_closure_set(v___f_2183_, 0, v_a_2172_);
lean_closure_set(v___f_2183_, 1, v_lctx_2182_);
v___x_2184_ = lean_unbox(v_a_2172_);
v___x_2185_ = lean_unbox(v_a_2172_);
lean_dec(v_a_2172_);
v___x_2186_ = l_Lean_Meta_letTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__2___redArg(v_e_2165_, v___f_2183_, v___x_2184_, v___x_2177_, v___x_2185_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_);
if (lean_obj_tag(v___x_2186_) == 0)
{
lean_object* v_a_2187_; lean_object* v___x_2189_; uint8_t v_isShared_2190_; uint8_t v_isSharedCheck_2196_; 
v_a_2187_ = lean_ctor_get(v___x_2186_, 0);
v_isSharedCheck_2196_ = !lean_is_exclusive(v___x_2186_);
if (v_isSharedCheck_2196_ == 0)
{
v___x_2189_ = v___x_2186_;
v_isShared_2190_ = v_isSharedCheck_2196_;
goto v_resetjp_2188_;
}
else
{
lean_inc(v_a_2187_);
lean_dec(v___x_2186_);
v___x_2189_ = lean_box(0);
v_isShared_2190_ = v_isSharedCheck_2196_;
goto v_resetjp_2188_;
}
v_resetjp_2188_:
{
lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2194_; 
v___x_2191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2191_, 0, v_a_2187_);
v___x_2192_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2192_, 0, v___x_2191_);
if (v_isShared_2190_ == 0)
{
lean_ctor_set(v___x_2189_, 0, v___x_2192_);
v___x_2194_ = v___x_2189_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v___x_2192_);
v___x_2194_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
return v___x_2194_;
}
}
}
else
{
lean_object* v_a_2197_; lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2204_; 
v_a_2197_ = lean_ctor_get(v___x_2186_, 0);
v_isSharedCheck_2204_ = !lean_is_exclusive(v___x_2186_);
if (v_isSharedCheck_2204_ == 0)
{
v___x_2199_ = v___x_2186_;
v_isShared_2200_ = v_isSharedCheck_2204_;
goto v_resetjp_2198_;
}
else
{
lean_inc(v_a_2197_);
lean_dec(v___x_2186_);
v___x_2199_ = lean_box(0);
v_isShared_2200_ = v_isSharedCheck_2204_;
goto v_resetjp_2198_;
}
v_resetjp_2198_:
{
lean_object* v___x_2202_; 
if (v_isShared_2200_ == 0)
{
v___x_2202_ = v___x_2199_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v_a_2197_);
v___x_2202_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
return v___x_2202_;
}
}
}
}
}
else
{
lean_object* v___x_2205_; lean_object* v___x_2207_; 
lean_dec(v_a_2172_);
lean_dec(v___y_2169_);
lean_dec_ref(v___y_2168_);
lean_dec(v___y_2167_);
lean_dec_ref(v___y_2166_);
v___x_2205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2205_, 0, v_e_2165_);
if (v_isShared_2175_ == 0)
{
lean_ctor_set(v___x_2174_, 0, v___x_2205_);
v___x_2207_ = v___x_2174_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v___x_2205_);
v___x_2207_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
return v___x_2207_;
}
}
}
}
else
{
lean_object* v_a_2210_; lean_object* v___x_2212_; uint8_t v_isShared_2213_; uint8_t v_isSharedCheck_2217_; 
lean_dec(v___y_2169_);
lean_dec_ref(v___y_2168_);
lean_dec(v___y_2167_);
lean_dec_ref(v___y_2166_);
lean_dec_ref(v_e_2165_);
v_a_2210_ = lean_ctor_get(v___x_2171_, 0);
v_isSharedCheck_2217_ = !lean_is_exclusive(v___x_2171_);
if (v_isSharedCheck_2217_ == 0)
{
v___x_2212_ = v___x_2171_;
v_isShared_2213_ = v_isSharedCheck_2217_;
goto v_resetjp_2211_;
}
else
{
lean_inc(v_a_2210_);
lean_dec(v___x_2171_);
v___x_2212_ = lean_box(0);
v_isShared_2213_ = v_isSharedCheck_2217_;
goto v_resetjp_2211_;
}
v_resetjp_2211_:
{
lean_object* v___x_2215_; 
if (v_isShared_2213_ == 0)
{
v___x_2215_ = v___x_2212_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v_a_2210_);
v___x_2215_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
return v___x_2215_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__2___boxed(lean_object* v_e_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_){
_start:
{
lean_object* v_res_2224_; 
v_res_2224_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__2(v_e_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_);
return v_res_2224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___lam__0(lean_object* v_00_u03b1_2225_, lean_object* v_x_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_){
_start:
{
lean_object* v___x_2232_; lean_object* v___x_2233_; 
v___x_2232_ = lean_apply_1(v_x_2226_, lean_box(0));
v___x_2233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2233_, 0, v___x_2232_);
return v___x_2233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___lam__0___boxed(lean_object* v_00_u03b1_2234_, lean_object* v_x_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_){
_start:
{
lean_object* v_res_2241_; 
v_res_2241_ = l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___lam__0(v_00_u03b1_2234_, v_x_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_);
lean_dec(v___y_2239_);
lean_dec_ref(v___y_2238_);
lean_dec(v___y_2237_);
lean_dec_ref(v___y_2236_);
return v_res_2241_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__3(void){
_start:
{
lean_object* v___x_2247_; lean_object* v___x_2248_; 
v___x_2247_ = l_Lean_maxRecDepthErrorMessage;
v___x_2248_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2248_, 0, v___x_2247_);
return v___x_2248_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__4(void){
_start:
{
lean_object* v___x_2249_; lean_object* v___x_2250_; 
v___x_2249_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__3);
v___x_2250_ = l_Lean_MessageData_ofFormat(v___x_2249_);
return v___x_2250_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__5(void){
_start:
{
lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; 
v___x_2251_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__4);
v___x_2252_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__2));
v___x_2253_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2253_, 0, v___x_2252_);
lean_ctor_set(v___x_2253_, 1, v___x_2251_);
return v___x_2253_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg(lean_object* v_ref_2254_){
_start:
{
lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; 
v___x_2256_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__5);
v___x_2257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2257_, 0, v_ref_2254_);
lean_ctor_set(v___x_2257_, 1, v___x_2256_);
v___x_2258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2258_, 0, v___x_2257_);
return v___x_2258_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___boxed(lean_object* v_ref_2259_, lean_object* v___y_2260_){
_start:
{
lean_object* v_res_2261_; 
v_res_2261_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg(v_ref_2259_);
return v_res_2261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12___redArg(lean_object* v_x_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_){
_start:
{
lean_object* v___y_2270_; lean_object* v_fileName_2279_; lean_object* v_fileMap_2280_; lean_object* v_options_2281_; lean_object* v_currRecDepth_2282_; lean_object* v_maxRecDepth_2283_; lean_object* v_ref_2284_; lean_object* v_currNamespace_2285_; lean_object* v_openDecls_2286_; lean_object* v_initHeartbeats_2287_; lean_object* v_maxHeartbeats_2288_; lean_object* v_quotContext_2289_; lean_object* v_currMacroScope_2290_; uint8_t v_diag_2291_; lean_object* v_cancelTk_x3f_2292_; uint8_t v_suppressElabErrors_2293_; lean_object* v_inheritedTraceOptions_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2306_; 
v_fileName_2279_ = lean_ctor_get(v___y_2266_, 0);
v_fileMap_2280_ = lean_ctor_get(v___y_2266_, 1);
v_options_2281_ = lean_ctor_get(v___y_2266_, 2);
v_currRecDepth_2282_ = lean_ctor_get(v___y_2266_, 3);
v_maxRecDepth_2283_ = lean_ctor_get(v___y_2266_, 4);
v_ref_2284_ = lean_ctor_get(v___y_2266_, 5);
v_currNamespace_2285_ = lean_ctor_get(v___y_2266_, 6);
v_openDecls_2286_ = lean_ctor_get(v___y_2266_, 7);
v_initHeartbeats_2287_ = lean_ctor_get(v___y_2266_, 8);
v_maxHeartbeats_2288_ = lean_ctor_get(v___y_2266_, 9);
v_quotContext_2289_ = lean_ctor_get(v___y_2266_, 10);
v_currMacroScope_2290_ = lean_ctor_get(v___y_2266_, 11);
v_diag_2291_ = lean_ctor_get_uint8(v___y_2266_, sizeof(void*)*14);
v_cancelTk_x3f_2292_ = lean_ctor_get(v___y_2266_, 12);
v_suppressElabErrors_2293_ = lean_ctor_get_uint8(v___y_2266_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2294_ = lean_ctor_get(v___y_2266_, 13);
v_isSharedCheck_2306_ = !lean_is_exclusive(v___y_2266_);
if (v_isSharedCheck_2306_ == 0)
{
v___x_2296_ = v___y_2266_;
v_isShared_2297_ = v_isSharedCheck_2306_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_inheritedTraceOptions_2294_);
lean_inc(v_cancelTk_x3f_2292_);
lean_inc(v_currMacroScope_2290_);
lean_inc(v_quotContext_2289_);
lean_inc(v_maxHeartbeats_2288_);
lean_inc(v_initHeartbeats_2287_);
lean_inc(v_openDecls_2286_);
lean_inc(v_currNamespace_2285_);
lean_inc(v_ref_2284_);
lean_inc(v_maxRecDepth_2283_);
lean_inc(v_currRecDepth_2282_);
lean_inc(v_options_2281_);
lean_inc(v_fileMap_2280_);
lean_inc(v_fileName_2279_);
lean_dec(v___y_2266_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2306_;
goto v_resetjp_2295_;
}
v___jp_2269_:
{
if (lean_obj_tag(v___y_2270_) == 0)
{
return v___y_2270_;
}
else
{
lean_object* v_a_2271_; lean_object* v___x_2273_; uint8_t v_isShared_2274_; uint8_t v_isSharedCheck_2278_; 
v_a_2271_ = lean_ctor_get(v___y_2270_, 0);
v_isSharedCheck_2278_ = !lean_is_exclusive(v___y_2270_);
if (v_isSharedCheck_2278_ == 0)
{
v___x_2273_ = v___y_2270_;
v_isShared_2274_ = v_isSharedCheck_2278_;
goto v_resetjp_2272_;
}
else
{
lean_inc(v_a_2271_);
lean_dec(v___y_2270_);
v___x_2273_ = lean_box(0);
v_isShared_2274_ = v_isSharedCheck_2278_;
goto v_resetjp_2272_;
}
v_resetjp_2272_:
{
lean_object* v___x_2276_; 
if (v_isShared_2274_ == 0)
{
v___x_2276_ = v___x_2273_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2277_; 
v_reuseFailAlloc_2277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2277_, 0, v_a_2271_);
v___x_2276_ = v_reuseFailAlloc_2277_;
goto v_reusejp_2275_;
}
v_reusejp_2275_:
{
return v___x_2276_;
}
}
}
}
v_resetjp_2295_:
{
uint8_t v___x_2298_; 
v___x_2298_ = lean_nat_dec_eq(v_currRecDepth_2282_, v_maxRecDepth_2283_);
if (v___x_2298_ == 0)
{
lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2302_; 
v___x_2299_ = lean_unsigned_to_nat(1u);
v___x_2300_ = lean_nat_add(v_currRecDepth_2282_, v___x_2299_);
lean_dec(v_currRecDepth_2282_);
if (v_isShared_2297_ == 0)
{
lean_ctor_set(v___x_2296_, 3, v___x_2300_);
v___x_2302_ = v___x_2296_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2304_; 
v_reuseFailAlloc_2304_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_2304_, 0, v_fileName_2279_);
lean_ctor_set(v_reuseFailAlloc_2304_, 1, v_fileMap_2280_);
lean_ctor_set(v_reuseFailAlloc_2304_, 2, v_options_2281_);
lean_ctor_set(v_reuseFailAlloc_2304_, 3, v___x_2300_);
lean_ctor_set(v_reuseFailAlloc_2304_, 4, v_maxRecDepth_2283_);
lean_ctor_set(v_reuseFailAlloc_2304_, 5, v_ref_2284_);
lean_ctor_set(v_reuseFailAlloc_2304_, 6, v_currNamespace_2285_);
lean_ctor_set(v_reuseFailAlloc_2304_, 7, v_openDecls_2286_);
lean_ctor_set(v_reuseFailAlloc_2304_, 8, v_initHeartbeats_2287_);
lean_ctor_set(v_reuseFailAlloc_2304_, 9, v_maxHeartbeats_2288_);
lean_ctor_set(v_reuseFailAlloc_2304_, 10, v_quotContext_2289_);
lean_ctor_set(v_reuseFailAlloc_2304_, 11, v_currMacroScope_2290_);
lean_ctor_set(v_reuseFailAlloc_2304_, 12, v_cancelTk_x3f_2292_);
lean_ctor_set(v_reuseFailAlloc_2304_, 13, v_inheritedTraceOptions_2294_);
lean_ctor_set_uint8(v_reuseFailAlloc_2304_, sizeof(void*)*14, v_diag_2291_);
lean_ctor_set_uint8(v_reuseFailAlloc_2304_, sizeof(void*)*14 + 1, v_suppressElabErrors_2293_);
v___x_2302_ = v_reuseFailAlloc_2304_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
lean_object* v___x_2303_; 
v___x_2303_ = lean_apply_6(v_x_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___x_2302_, v___y_2267_, lean_box(0));
v___y_2270_ = v___x_2303_;
goto v___jp_2269_;
}
}
else
{
lean_object* v___x_2305_; 
lean_del_object(v___x_2296_);
lean_dec_ref(v_inheritedTraceOptions_2294_);
lean_dec(v_cancelTk_x3f_2292_);
lean_dec(v_currMacroScope_2290_);
lean_dec(v_quotContext_2289_);
lean_dec(v_maxHeartbeats_2288_);
lean_dec(v_initHeartbeats_2287_);
lean_dec(v_openDecls_2286_);
lean_dec(v_currNamespace_2285_);
lean_dec(v_maxRecDepth_2283_);
lean_dec(v_currRecDepth_2282_);
lean_dec_ref(v_options_2281_);
lean_dec_ref(v_fileMap_2280_);
lean_dec_ref(v_fileName_2279_);
lean_dec(v___y_2267_);
lean_dec(v___y_2265_);
lean_dec_ref(v___y_2264_);
lean_dec(v___y_2263_);
lean_dec_ref(v_x_2262_);
v___x_2305_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg(v_ref_2284_);
v___y_2270_ = v___x_2305_;
goto v___jp_2269_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12___redArg___boxed(lean_object* v_x_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_){
_start:
{
lean_object* v_res_2314_; 
v_res_2314_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12___redArg(v_x_2307_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_);
return v_res_2314_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7_spec__8___redArg(lean_object* v_a_2315_, lean_object* v_x_2316_){
_start:
{
if (lean_obj_tag(v_x_2316_) == 0)
{
lean_object* v___x_2317_; 
v___x_2317_ = lean_box(0);
return v___x_2317_;
}
else
{
lean_object* v_key_2318_; lean_object* v_value_2319_; lean_object* v_tail_2320_; uint8_t v___x_2321_; 
v_key_2318_ = lean_ctor_get(v_x_2316_, 0);
v_value_2319_ = lean_ctor_get(v_x_2316_, 1);
v_tail_2320_ = lean_ctor_get(v_x_2316_, 2);
v___x_2321_ = l_Lean_ExprStructEq_beq(v_key_2318_, v_a_2315_);
if (v___x_2321_ == 0)
{
v_x_2316_ = v_tail_2320_;
goto _start;
}
else
{
lean_object* v___x_2323_; 
lean_inc(v_value_2319_);
v___x_2323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2323_, 0, v_value_2319_);
return v___x_2323_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7_spec__8___redArg___boxed(lean_object* v_a_2324_, lean_object* v_x_2325_){
_start:
{
lean_object* v_res_2326_; 
v_res_2326_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7_spec__8___redArg(v_a_2324_, v_x_2325_);
lean_dec(v_x_2325_);
lean_dec_ref(v_a_2324_);
return v_res_2326_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___redArg(lean_object* v_m_2327_, lean_object* v_a_2328_){
_start:
{
lean_object* v_buckets_2329_; lean_object* v___x_2330_; uint64_t v___x_2331_; uint64_t v___x_2332_; uint64_t v___x_2333_; uint64_t v_fold_2334_; uint64_t v___x_2335_; uint64_t v___x_2336_; uint64_t v___x_2337_; size_t v___x_2338_; size_t v___x_2339_; size_t v___x_2340_; size_t v___x_2341_; size_t v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; 
v_buckets_2329_ = lean_ctor_get(v_m_2327_, 1);
v___x_2330_ = lean_array_get_size(v_buckets_2329_);
v___x_2331_ = l_Lean_ExprStructEq_hash(v_a_2328_);
v___x_2332_ = 32ULL;
v___x_2333_ = lean_uint64_shift_right(v___x_2331_, v___x_2332_);
v_fold_2334_ = lean_uint64_xor(v___x_2331_, v___x_2333_);
v___x_2335_ = 16ULL;
v___x_2336_ = lean_uint64_shift_right(v_fold_2334_, v___x_2335_);
v___x_2337_ = lean_uint64_xor(v_fold_2334_, v___x_2336_);
v___x_2338_ = lean_uint64_to_usize(v___x_2337_);
v___x_2339_ = lean_usize_of_nat(v___x_2330_);
v___x_2340_ = ((size_t)1ULL);
v___x_2341_ = lean_usize_sub(v___x_2339_, v___x_2340_);
v___x_2342_ = lean_usize_land(v___x_2338_, v___x_2341_);
v___x_2343_ = lean_array_uget_borrowed(v_buckets_2329_, v___x_2342_);
v___x_2344_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7_spec__8___redArg(v_a_2328_, v___x_2343_);
return v___x_2344_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___redArg___boxed(lean_object* v_m_2345_, lean_object* v_a_2346_){
_start:
{
lean_object* v_res_2347_; 
v_res_2347_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___redArg(v_m_2345_, v_a_2346_);
lean_dec_ref(v_a_2346_);
lean_dec_ref(v_m_2345_);
return v_res_2347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg___lam__0(lean_object* v_k_2348_, lean_object* v___y_2349_, lean_object* v_b_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_){
_start:
{
lean_object* v___x_2356_; 
v___x_2356_ = lean_apply_7(v_k_2348_, v_b_2350_, v___y_2349_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_, lean_box(0));
return v___x_2356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg___lam__0___boxed(lean_object* v_k_2357_, lean_object* v___y_2358_, lean_object* v_b_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_){
_start:
{
lean_object* v_res_2365_; 
v_res_2365_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg___lam__0(v_k_2357_, v___y_2358_, v_b_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_);
return v_res_2365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg(lean_object* v_name_2366_, uint8_t v_bi_2367_, lean_object* v_type_2368_, lean_object* v_k_2369_, uint8_t v_kind_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_){
_start:
{
lean_object* v___f_2377_; lean_object* v___x_2378_; 
v___f_2377_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2377_, 0, v_k_2369_);
lean_closure_set(v___f_2377_, 1, v___y_2371_);
v___x_2378_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2366_, v_bi_2367_, v_type_2368_, v___f_2377_, v_kind_2370_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_);
if (lean_obj_tag(v___x_2378_) == 0)
{
return v___x_2378_;
}
else
{
lean_object* v_a_2379_; lean_object* v___x_2381_; uint8_t v_isShared_2382_; uint8_t v_isSharedCheck_2386_; 
v_a_2379_ = lean_ctor_get(v___x_2378_, 0);
v_isSharedCheck_2386_ = !lean_is_exclusive(v___x_2378_);
if (v_isSharedCheck_2386_ == 0)
{
v___x_2381_ = v___x_2378_;
v_isShared_2382_ = v_isSharedCheck_2386_;
goto v_resetjp_2380_;
}
else
{
lean_inc(v_a_2379_);
lean_dec(v___x_2378_);
v___x_2381_ = lean_box(0);
v_isShared_2382_ = v_isSharedCheck_2386_;
goto v_resetjp_2380_;
}
v_resetjp_2380_:
{
lean_object* v___x_2384_; 
if (v_isShared_2382_ == 0)
{
v___x_2384_ = v___x_2381_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v_a_2379_);
v___x_2384_ = v_reuseFailAlloc_2385_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
return v___x_2384_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg___boxed(lean_object* v_name_2387_, lean_object* v_bi_2388_, lean_object* v_type_2389_, lean_object* v_k_2390_, lean_object* v_kind_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_){
_start:
{
uint8_t v_bi_boxed_2398_; uint8_t v_kind_boxed_2399_; lean_object* v_res_2400_; 
v_bi_boxed_2398_ = lean_unbox(v_bi_2388_);
v_kind_boxed_2399_ = lean_unbox(v_kind_2391_);
v_res_2400_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg(v_name_2387_, v_bi_boxed_2398_, v_type_2389_, v_k_2390_, v_kind_boxed_2399_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_);
return v_res_2400_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___lam__2(lean_object* v___x_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_){
_start:
{
lean_object* v___x_2407_; 
v___x_2407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2407_, 0, v___x_2401_);
return v___x_2407_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___lam__2___boxed(lean_object* v___x_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_){
_start:
{
lean_object* v_res_2414_; 
v_res_2414_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___lam__2(v___x_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_);
lean_dec(v___y_2412_);
lean_dec_ref(v___y_2411_);
lean_dec(v___y_2410_);
lean_dec_ref(v___y_2409_);
return v_res_2414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13___redArg(lean_object* v_name_2415_, lean_object* v_type_2416_, lean_object* v_val_2417_, lean_object* v_k_2418_, uint8_t v_nondep_2419_, uint8_t v_kind_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_){
_start:
{
lean_object* v___f_2427_; lean_object* v___x_2428_; 
v___f_2427_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2427_, 0, v_k_2418_);
lean_closure_set(v___f_2427_, 1, v___y_2421_);
v___x_2428_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_2415_, v_type_2416_, v_val_2417_, v___f_2427_, v_nondep_2419_, v_kind_2420_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_);
if (lean_obj_tag(v___x_2428_) == 0)
{
return v___x_2428_;
}
else
{
lean_object* v_a_2429_; lean_object* v___x_2431_; uint8_t v_isShared_2432_; uint8_t v_isSharedCheck_2436_; 
v_a_2429_ = lean_ctor_get(v___x_2428_, 0);
v_isSharedCheck_2436_ = !lean_is_exclusive(v___x_2428_);
if (v_isSharedCheck_2436_ == 0)
{
v___x_2431_ = v___x_2428_;
v_isShared_2432_ = v_isSharedCheck_2436_;
goto v_resetjp_2430_;
}
else
{
lean_inc(v_a_2429_);
lean_dec(v___x_2428_);
v___x_2431_ = lean_box(0);
v_isShared_2432_ = v_isSharedCheck_2436_;
goto v_resetjp_2430_;
}
v_resetjp_2430_:
{
lean_object* v___x_2434_; 
if (v_isShared_2432_ == 0)
{
v___x_2434_ = v___x_2431_;
goto v_reusejp_2433_;
}
else
{
lean_object* v_reuseFailAlloc_2435_; 
v_reuseFailAlloc_2435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2435_, 0, v_a_2429_);
v___x_2434_ = v_reuseFailAlloc_2435_;
goto v_reusejp_2433_;
}
v_reusejp_2433_:
{
return v___x_2434_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13___redArg___boxed(lean_object* v_name_2437_, lean_object* v_type_2438_, lean_object* v_val_2439_, lean_object* v_k_2440_, lean_object* v_nondep_2441_, lean_object* v_kind_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_){
_start:
{
uint8_t v_nondep_boxed_2449_; uint8_t v_kind_boxed_2450_; lean_object* v_res_2451_; 
v_nondep_boxed_2449_ = lean_unbox(v_nondep_2441_);
v_kind_boxed_2450_ = lean_unbox(v_kind_2442_);
v_res_2451_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13___redArg(v_name_2437_, v_type_2438_, v_val_2439_, v_k_2440_, v_nondep_boxed_2449_, v_kind_boxed_2450_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_);
return v_res_2451_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__0(lean_object* v_00_u03b1_2452_, lean_object* v_x_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_){
_start:
{
lean_object* v___x_2459_; lean_object* v___x_2460_; 
v___x_2459_ = lean_apply_1(v_x_2453_, lean_box(0));
v___x_2460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2460_, 0, v___x_2459_);
return v___x_2460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__0___boxed(lean_object* v_00_u03b1_2461_, lean_object* v_x_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_){
_start:
{
lean_object* v_res_2468_; 
v_res_2468_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__0(v_00_u03b1_2461_, v_x_2462_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_);
lean_dec(v___y_2466_);
lean_dec_ref(v___y_2465_);
lean_dec(v___y_2464_);
lean_dec_ref(v___y_2463_);
return v_res_2468_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18___redArg(lean_object* v_a_2469_, lean_object* v_x_2470_){
_start:
{
if (lean_obj_tag(v_x_2470_) == 0)
{
uint8_t v___x_2471_; 
v___x_2471_ = 0;
return v___x_2471_;
}
else
{
lean_object* v_key_2472_; lean_object* v_tail_2473_; uint8_t v___x_2474_; 
v_key_2472_ = lean_ctor_get(v_x_2470_, 0);
v_tail_2473_ = lean_ctor_get(v_x_2470_, 2);
v___x_2474_ = l_Lean_ExprStructEq_beq(v_key_2472_, v_a_2469_);
if (v___x_2474_ == 0)
{
v_x_2470_ = v_tail_2473_;
goto _start;
}
else
{
return v___x_2474_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18___redArg___boxed(lean_object* v_a_2476_, lean_object* v_x_2477_){
_start:
{
uint8_t v_res_2478_; lean_object* v_r_2479_; 
v_res_2478_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18___redArg(v_a_2476_, v_x_2477_);
lean_dec(v_x_2477_);
lean_dec_ref(v_a_2476_);
v_r_2479_ = lean_box(v_res_2478_);
return v_r_2479_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__20___redArg(lean_object* v_a_2480_, lean_object* v_b_2481_, lean_object* v_x_2482_){
_start:
{
if (lean_obj_tag(v_x_2482_) == 0)
{
lean_dec(v_b_2481_);
lean_dec_ref(v_a_2480_);
return v_x_2482_;
}
else
{
lean_object* v_key_2483_; lean_object* v_value_2484_; lean_object* v_tail_2485_; lean_object* v___x_2487_; uint8_t v_isShared_2488_; uint8_t v_isSharedCheck_2497_; 
v_key_2483_ = lean_ctor_get(v_x_2482_, 0);
v_value_2484_ = lean_ctor_get(v_x_2482_, 1);
v_tail_2485_ = lean_ctor_get(v_x_2482_, 2);
v_isSharedCheck_2497_ = !lean_is_exclusive(v_x_2482_);
if (v_isSharedCheck_2497_ == 0)
{
v___x_2487_ = v_x_2482_;
v_isShared_2488_ = v_isSharedCheck_2497_;
goto v_resetjp_2486_;
}
else
{
lean_inc(v_tail_2485_);
lean_inc(v_value_2484_);
lean_inc(v_key_2483_);
lean_dec(v_x_2482_);
v___x_2487_ = lean_box(0);
v_isShared_2488_ = v_isSharedCheck_2497_;
goto v_resetjp_2486_;
}
v_resetjp_2486_:
{
uint8_t v___x_2489_; 
v___x_2489_ = l_Lean_ExprStructEq_beq(v_key_2483_, v_a_2480_);
if (v___x_2489_ == 0)
{
lean_object* v___x_2490_; lean_object* v___x_2492_; 
v___x_2490_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__20___redArg(v_a_2480_, v_b_2481_, v_tail_2485_);
if (v_isShared_2488_ == 0)
{
lean_ctor_set(v___x_2487_, 2, v___x_2490_);
v___x_2492_ = v___x_2487_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v_key_2483_);
lean_ctor_set(v_reuseFailAlloc_2493_, 1, v_value_2484_);
lean_ctor_set(v_reuseFailAlloc_2493_, 2, v___x_2490_);
v___x_2492_ = v_reuseFailAlloc_2493_;
goto v_reusejp_2491_;
}
v_reusejp_2491_:
{
return v___x_2492_;
}
}
else
{
lean_object* v___x_2495_; 
lean_dec(v_value_2484_);
lean_dec(v_key_2483_);
if (v_isShared_2488_ == 0)
{
lean_ctor_set(v___x_2487_, 1, v_b_2481_);
lean_ctor_set(v___x_2487_, 0, v_a_2480_);
v___x_2495_ = v___x_2487_;
goto v_reusejp_2494_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2496_, 0, v_a_2480_);
lean_ctor_set(v_reuseFailAlloc_2496_, 1, v_b_2481_);
lean_ctor_set(v_reuseFailAlloc_2496_, 2, v_tail_2485_);
v___x_2495_ = v_reuseFailAlloc_2496_;
goto v_reusejp_2494_;
}
v_reusejp_2494_:
{
return v___x_2495_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19_spec__20_spec__21___redArg(lean_object* v_x_2498_, lean_object* v_x_2499_){
_start:
{
if (lean_obj_tag(v_x_2499_) == 0)
{
return v_x_2498_;
}
else
{
lean_object* v_key_2500_; lean_object* v_value_2501_; lean_object* v_tail_2502_; lean_object* v___x_2504_; uint8_t v_isShared_2505_; uint8_t v_isSharedCheck_2525_; 
v_key_2500_ = lean_ctor_get(v_x_2499_, 0);
v_value_2501_ = lean_ctor_get(v_x_2499_, 1);
v_tail_2502_ = lean_ctor_get(v_x_2499_, 2);
v_isSharedCheck_2525_ = !lean_is_exclusive(v_x_2499_);
if (v_isSharedCheck_2525_ == 0)
{
v___x_2504_ = v_x_2499_;
v_isShared_2505_ = v_isSharedCheck_2525_;
goto v_resetjp_2503_;
}
else
{
lean_inc(v_tail_2502_);
lean_inc(v_value_2501_);
lean_inc(v_key_2500_);
lean_dec(v_x_2499_);
v___x_2504_ = lean_box(0);
v_isShared_2505_ = v_isSharedCheck_2525_;
goto v_resetjp_2503_;
}
v_resetjp_2503_:
{
lean_object* v___x_2506_; uint64_t v___x_2507_; uint64_t v___x_2508_; uint64_t v___x_2509_; uint64_t v_fold_2510_; uint64_t v___x_2511_; uint64_t v___x_2512_; uint64_t v___x_2513_; size_t v___x_2514_; size_t v___x_2515_; size_t v___x_2516_; size_t v___x_2517_; size_t v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2521_; 
v___x_2506_ = lean_array_get_size(v_x_2498_);
v___x_2507_ = l_Lean_ExprStructEq_hash(v_key_2500_);
v___x_2508_ = 32ULL;
v___x_2509_ = lean_uint64_shift_right(v___x_2507_, v___x_2508_);
v_fold_2510_ = lean_uint64_xor(v___x_2507_, v___x_2509_);
v___x_2511_ = 16ULL;
v___x_2512_ = lean_uint64_shift_right(v_fold_2510_, v___x_2511_);
v___x_2513_ = lean_uint64_xor(v_fold_2510_, v___x_2512_);
v___x_2514_ = lean_uint64_to_usize(v___x_2513_);
v___x_2515_ = lean_usize_of_nat(v___x_2506_);
v___x_2516_ = ((size_t)1ULL);
v___x_2517_ = lean_usize_sub(v___x_2515_, v___x_2516_);
v___x_2518_ = lean_usize_land(v___x_2514_, v___x_2517_);
v___x_2519_ = lean_array_uget_borrowed(v_x_2498_, v___x_2518_);
lean_inc(v___x_2519_);
if (v_isShared_2505_ == 0)
{
lean_ctor_set(v___x_2504_, 2, v___x_2519_);
v___x_2521_ = v___x_2504_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v_key_2500_);
lean_ctor_set(v_reuseFailAlloc_2524_, 1, v_value_2501_);
lean_ctor_set(v_reuseFailAlloc_2524_, 2, v___x_2519_);
v___x_2521_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
lean_object* v___x_2522_; 
v___x_2522_ = lean_array_uset(v_x_2498_, v___x_2518_, v___x_2521_);
v_x_2498_ = v___x_2522_;
v_x_2499_ = v_tail_2502_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19_spec__20___redArg(lean_object* v_i_2526_, lean_object* v_source_2527_, lean_object* v_target_2528_){
_start:
{
lean_object* v___x_2529_; uint8_t v___x_2530_; 
v___x_2529_ = lean_array_get_size(v_source_2527_);
v___x_2530_ = lean_nat_dec_lt(v_i_2526_, v___x_2529_);
if (v___x_2530_ == 0)
{
lean_dec_ref(v_source_2527_);
lean_dec(v_i_2526_);
return v_target_2528_;
}
else
{
lean_object* v_es_2531_; lean_object* v___x_2532_; lean_object* v_source_2533_; lean_object* v_target_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; 
v_es_2531_ = lean_array_fget(v_source_2527_, v_i_2526_);
v___x_2532_ = lean_box(0);
v_source_2533_ = lean_array_fset(v_source_2527_, v_i_2526_, v___x_2532_);
v_target_2534_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19_spec__20_spec__21___redArg(v_target_2528_, v_es_2531_);
v___x_2535_ = lean_unsigned_to_nat(1u);
v___x_2536_ = lean_nat_add(v_i_2526_, v___x_2535_);
lean_dec(v_i_2526_);
v_i_2526_ = v___x_2536_;
v_source_2527_ = v_source_2533_;
v_target_2528_ = v_target_2534_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19___redArg(lean_object* v_data_2538_){
_start:
{
lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v_nbuckets_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; 
v___x_2539_ = lean_array_get_size(v_data_2538_);
v___x_2540_ = lean_unsigned_to_nat(2u);
v_nbuckets_2541_ = lean_nat_mul(v___x_2539_, v___x_2540_);
v___x_2542_ = lean_unsigned_to_nat(0u);
v___x_2543_ = lean_box(0);
v___x_2544_ = lean_mk_array(v_nbuckets_2541_, v___x_2543_);
v___x_2545_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19_spec__20___redArg(v___x_2542_, v_data_2538_, v___x_2544_);
return v___x_2545_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13___redArg(lean_object* v_m_2546_, lean_object* v_a_2547_, lean_object* v_b_2548_){
_start:
{
lean_object* v_size_2549_; lean_object* v_buckets_2550_; lean_object* v___x_2552_; uint8_t v_isShared_2553_; uint8_t v_isSharedCheck_2593_; 
v_size_2549_ = lean_ctor_get(v_m_2546_, 0);
v_buckets_2550_ = lean_ctor_get(v_m_2546_, 1);
v_isSharedCheck_2593_ = !lean_is_exclusive(v_m_2546_);
if (v_isSharedCheck_2593_ == 0)
{
v___x_2552_ = v_m_2546_;
v_isShared_2553_ = v_isSharedCheck_2593_;
goto v_resetjp_2551_;
}
else
{
lean_inc(v_buckets_2550_);
lean_inc(v_size_2549_);
lean_dec(v_m_2546_);
v___x_2552_ = lean_box(0);
v_isShared_2553_ = v_isSharedCheck_2593_;
goto v_resetjp_2551_;
}
v_resetjp_2551_:
{
lean_object* v___x_2554_; uint64_t v___x_2555_; uint64_t v___x_2556_; uint64_t v___x_2557_; uint64_t v_fold_2558_; uint64_t v___x_2559_; uint64_t v___x_2560_; uint64_t v___x_2561_; size_t v___x_2562_; size_t v___x_2563_; size_t v___x_2564_; size_t v___x_2565_; size_t v___x_2566_; lean_object* v_bkt_2567_; uint8_t v___x_2568_; 
v___x_2554_ = lean_array_get_size(v_buckets_2550_);
v___x_2555_ = l_Lean_ExprStructEq_hash(v_a_2547_);
v___x_2556_ = 32ULL;
v___x_2557_ = lean_uint64_shift_right(v___x_2555_, v___x_2556_);
v_fold_2558_ = lean_uint64_xor(v___x_2555_, v___x_2557_);
v___x_2559_ = 16ULL;
v___x_2560_ = lean_uint64_shift_right(v_fold_2558_, v___x_2559_);
v___x_2561_ = lean_uint64_xor(v_fold_2558_, v___x_2560_);
v___x_2562_ = lean_uint64_to_usize(v___x_2561_);
v___x_2563_ = lean_usize_of_nat(v___x_2554_);
v___x_2564_ = ((size_t)1ULL);
v___x_2565_ = lean_usize_sub(v___x_2563_, v___x_2564_);
v___x_2566_ = lean_usize_land(v___x_2562_, v___x_2565_);
v_bkt_2567_ = lean_array_uget_borrowed(v_buckets_2550_, v___x_2566_);
v___x_2568_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18___redArg(v_a_2547_, v_bkt_2567_);
if (v___x_2568_ == 0)
{
lean_object* v___x_2569_; lean_object* v_size_x27_2570_; lean_object* v___x_2571_; lean_object* v_buckets_x27_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; uint8_t v___x_2578_; 
v___x_2569_ = lean_unsigned_to_nat(1u);
v_size_x27_2570_ = lean_nat_add(v_size_2549_, v___x_2569_);
lean_dec(v_size_2549_);
lean_inc(v_bkt_2567_);
v___x_2571_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2571_, 0, v_a_2547_);
lean_ctor_set(v___x_2571_, 1, v_b_2548_);
lean_ctor_set(v___x_2571_, 2, v_bkt_2567_);
v_buckets_x27_2572_ = lean_array_uset(v_buckets_2550_, v___x_2566_, v___x_2571_);
v___x_2573_ = lean_unsigned_to_nat(4u);
v___x_2574_ = lean_nat_mul(v_size_x27_2570_, v___x_2573_);
v___x_2575_ = lean_unsigned_to_nat(3u);
v___x_2576_ = lean_nat_div(v___x_2574_, v___x_2575_);
lean_dec(v___x_2574_);
v___x_2577_ = lean_array_get_size(v_buckets_x27_2572_);
v___x_2578_ = lean_nat_dec_le(v___x_2576_, v___x_2577_);
lean_dec(v___x_2576_);
if (v___x_2578_ == 0)
{
lean_object* v_val_2579_; lean_object* v___x_2581_; 
v_val_2579_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19___redArg(v_buckets_x27_2572_);
if (v_isShared_2553_ == 0)
{
lean_ctor_set(v___x_2552_, 1, v_val_2579_);
lean_ctor_set(v___x_2552_, 0, v_size_x27_2570_);
v___x_2581_ = v___x_2552_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v_size_x27_2570_);
lean_ctor_set(v_reuseFailAlloc_2582_, 1, v_val_2579_);
v___x_2581_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
return v___x_2581_;
}
}
else
{
lean_object* v___x_2584_; 
if (v_isShared_2553_ == 0)
{
lean_ctor_set(v___x_2552_, 1, v_buckets_x27_2572_);
lean_ctor_set(v___x_2552_, 0, v_size_x27_2570_);
v___x_2584_ = v___x_2552_;
goto v_reusejp_2583_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v_size_x27_2570_);
lean_ctor_set(v_reuseFailAlloc_2585_, 1, v_buckets_x27_2572_);
v___x_2584_ = v_reuseFailAlloc_2585_;
goto v_reusejp_2583_;
}
v_reusejp_2583_:
{
return v___x_2584_;
}
}
}
else
{
lean_object* v___x_2586_; lean_object* v_buckets_x27_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2591_; 
lean_inc(v_bkt_2567_);
v___x_2586_ = lean_box(0);
v_buckets_x27_2587_ = lean_array_uset(v_buckets_2550_, v___x_2566_, v___x_2586_);
v___x_2588_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__20___redArg(v_a_2547_, v_b_2548_, v_bkt_2567_);
v___x_2589_ = lean_array_uset(v_buckets_x27_2587_, v___x_2566_, v___x_2588_);
if (v_isShared_2553_ == 0)
{
lean_ctor_set(v___x_2552_, 1, v___x_2589_);
v___x_2591_ = v___x_2552_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2592_; 
v_reuseFailAlloc_2592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2592_, 0, v_size_2549_);
lean_ctor_set(v_reuseFailAlloc_2592_, 1, v___x_2589_);
v___x_2591_ = v_reuseFailAlloc_2592_;
goto v_reusejp_2590_;
}
v_reusejp_2590_:
{
return v___x_2591_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__2(lean_object* v_a_2594_, lean_object* v_e_2595_, lean_object* v_a_2596_){
_start:
{
lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; 
v___x_2598_ = lean_st_ref_take(v_a_2594_);
v___x_2599_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13___redArg(v___x_2598_, v_e_2595_, v_a_2596_);
v___x_2600_ = lean_st_ref_set(v_a_2594_, v___x_2599_);
v___x_2601_ = lean_box(0);
return v___x_2601_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__2___boxed(lean_object* v_a_2602_, lean_object* v_e_2603_, lean_object* v_a_2604_, lean_object* v___y_2605_){
_start:
{
lean_object* v_res_2606_; 
v_res_2606_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__2(v_a_2602_, v_e_2603_, v_a_2604_);
lean_dec(v_a_2602_);
return v_res_2606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9___lam__0(lean_object* v_fvars_2609_, lean_object* v_pre_2610_, lean_object* v_post_2611_, uint8_t v_usedLetOnly_2612_, uint8_t v_skipConstInApp_2613_, uint8_t v_skipInstances_2614_, lean_object* v_body_2615_, lean_object* v_x_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_){
_start:
{
lean_object* v___x_2623_; lean_object* v___x_2624_; 
v___x_2623_ = lean_array_push(v_fvars_2609_, v_x_2616_);
v___x_2624_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9(v_pre_2610_, v_post_2611_, v_usedLetOnly_2612_, v_skipConstInApp_2613_, v_skipInstances_2614_, v___x_2623_, v_body_2615_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_);
return v___x_2624_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9___lam__0___boxed(lean_object* v_fvars_2625_, lean_object* v_pre_2626_, lean_object* v_post_2627_, lean_object* v_usedLetOnly_2628_, lean_object* v_skipConstInApp_2629_, lean_object* v_skipInstances_2630_, lean_object* v_body_2631_, lean_object* v_x_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_){
_start:
{
uint8_t v_usedLetOnly_boxed_2639_; uint8_t v_skipConstInApp_boxed_2640_; uint8_t v_skipInstances_boxed_2641_; lean_object* v_res_2642_; 
v_usedLetOnly_boxed_2639_ = lean_unbox(v_usedLetOnly_2628_);
v_skipConstInApp_boxed_2640_ = lean_unbox(v_skipConstInApp_2629_);
v_skipInstances_boxed_2641_ = lean_unbox(v_skipInstances_2630_);
v_res_2642_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9___lam__0(v_fvars_2625_, v_pre_2626_, v_post_2627_, v_usedLetOnly_boxed_2639_, v_skipConstInApp_boxed_2640_, v_skipInstances_boxed_2641_, v_body_2631_, v_x_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_);
return v_res_2642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(lean_object* v_pre_2643_, lean_object* v_post_2644_, uint8_t v_usedLetOnly_2645_, uint8_t v_skipConstInApp_2646_, uint8_t v_skipInstances_2647_, lean_object* v_e_2648_, lean_object* v_a_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_){
_start:
{
lean_object* v___x_2655_; 
lean_inc_ref(v_post_2644_);
lean_inc(v___y_2653_);
lean_inc_ref(v___y_2652_);
lean_inc(v___y_2651_);
lean_inc_ref(v___y_2650_);
lean_inc_ref(v_e_2648_);
v___x_2655_ = lean_apply_6(v_post_2644_, v_e_2648_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_, lean_box(0));
if (lean_obj_tag(v___x_2655_) == 0)
{
lean_object* v_a_2656_; lean_object* v___x_2658_; uint8_t v_isShared_2659_; uint8_t v_isSharedCheck_2674_; 
v_a_2656_ = lean_ctor_get(v___x_2655_, 0);
v_isSharedCheck_2674_ = !lean_is_exclusive(v___x_2655_);
if (v_isSharedCheck_2674_ == 0)
{
v___x_2658_ = v___x_2655_;
v_isShared_2659_ = v_isSharedCheck_2674_;
goto v_resetjp_2657_;
}
else
{
lean_inc(v_a_2656_);
lean_dec(v___x_2655_);
v___x_2658_ = lean_box(0);
v_isShared_2659_ = v_isSharedCheck_2674_;
goto v_resetjp_2657_;
}
v_resetjp_2657_:
{
switch(lean_obj_tag(v_a_2656_))
{
case 0:
{
lean_object* v_e_2660_; lean_object* v___x_2662_; 
lean_dec(v___y_2653_);
lean_dec_ref(v___y_2652_);
lean_dec(v___y_2651_);
lean_dec_ref(v___y_2650_);
lean_dec(v_a_2649_);
lean_dec_ref(v_e_2648_);
lean_dec_ref(v_post_2644_);
lean_dec_ref(v_pre_2643_);
v_e_2660_ = lean_ctor_get(v_a_2656_, 0);
lean_inc_ref(v_e_2660_);
lean_dec_ref(v_a_2656_);
if (v_isShared_2659_ == 0)
{
lean_ctor_set(v___x_2658_, 0, v_e_2660_);
v___x_2662_ = v___x_2658_;
goto v_reusejp_2661_;
}
else
{
lean_object* v_reuseFailAlloc_2663_; 
v_reuseFailAlloc_2663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2663_, 0, v_e_2660_);
v___x_2662_ = v_reuseFailAlloc_2663_;
goto v_reusejp_2661_;
}
v_reusejp_2661_:
{
return v___x_2662_;
}
}
case 1:
{
lean_object* v_e_2664_; lean_object* v___x_2665_; 
lean_del_object(v___x_2658_);
lean_dec_ref(v_e_2648_);
v_e_2664_ = lean_ctor_get(v_a_2656_, 0);
lean_inc_ref(v_e_2664_);
lean_dec_ref(v_a_2656_);
v___x_2665_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2643_, v_post_2644_, v_usedLetOnly_2645_, v_skipConstInApp_2646_, v_skipInstances_2647_, v_e_2664_, v_a_2649_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_);
return v___x_2665_;
}
default: 
{
lean_object* v_e_x3f_2666_; 
lean_dec(v___y_2653_);
lean_dec_ref(v___y_2652_);
lean_dec(v___y_2651_);
lean_dec_ref(v___y_2650_);
lean_dec(v_a_2649_);
lean_dec_ref(v_post_2644_);
lean_dec_ref(v_pre_2643_);
v_e_x3f_2666_ = lean_ctor_get(v_a_2656_, 0);
lean_inc(v_e_x3f_2666_);
lean_dec_ref(v_a_2656_);
if (lean_obj_tag(v_e_x3f_2666_) == 0)
{
lean_object* v___x_2668_; 
if (v_isShared_2659_ == 0)
{
lean_ctor_set(v___x_2658_, 0, v_e_2648_);
v___x_2668_ = v___x_2658_;
goto v_reusejp_2667_;
}
else
{
lean_object* v_reuseFailAlloc_2669_; 
v_reuseFailAlloc_2669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2669_, 0, v_e_2648_);
v___x_2668_ = v_reuseFailAlloc_2669_;
goto v_reusejp_2667_;
}
v_reusejp_2667_:
{
return v___x_2668_;
}
}
else
{
lean_object* v_val_2670_; lean_object* v___x_2672_; 
lean_dec_ref(v_e_2648_);
v_val_2670_ = lean_ctor_get(v_e_x3f_2666_, 0);
lean_inc(v_val_2670_);
lean_dec_ref(v_e_x3f_2666_);
if (v_isShared_2659_ == 0)
{
lean_ctor_set(v___x_2658_, 0, v_val_2670_);
v___x_2672_ = v___x_2658_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v_val_2670_);
v___x_2672_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
return v___x_2672_;
}
}
}
}
}
}
else
{
lean_object* v_a_2675_; lean_object* v___x_2677_; uint8_t v_isShared_2678_; uint8_t v_isSharedCheck_2682_; 
lean_dec(v___y_2653_);
lean_dec_ref(v___y_2652_);
lean_dec(v___y_2651_);
lean_dec_ref(v___y_2650_);
lean_dec(v_a_2649_);
lean_dec_ref(v_e_2648_);
lean_dec_ref(v_post_2644_);
lean_dec_ref(v_pre_2643_);
v_a_2675_ = lean_ctor_get(v___x_2655_, 0);
v_isSharedCheck_2682_ = !lean_is_exclusive(v___x_2655_);
if (v_isSharedCheck_2682_ == 0)
{
v___x_2677_ = v___x_2655_;
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
else
{
lean_inc(v_a_2675_);
lean_dec(v___x_2655_);
v___x_2677_ = lean_box(0);
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
v_resetjp_2676_:
{
lean_object* v___x_2680_; 
if (v_isShared_2678_ == 0)
{
v___x_2680_ = v___x_2677_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v_a_2675_);
v___x_2680_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
return v___x_2680_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9(lean_object* v_pre_2683_, lean_object* v_post_2684_, uint8_t v_usedLetOnly_2685_, uint8_t v_skipConstInApp_2686_, uint8_t v_skipInstances_2687_, lean_object* v_fvars_2688_, lean_object* v_e_2689_, lean_object* v_a_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_){
_start:
{
if (lean_obj_tag(v_e_2689_) == 6)
{
lean_object* v_binderName_2696_; lean_object* v_binderType_2697_; lean_object* v_body_2698_; uint8_t v_binderInfo_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; 
v_binderName_2696_ = lean_ctor_get(v_e_2689_, 0);
lean_inc(v_binderName_2696_);
v_binderType_2697_ = lean_ctor_get(v_e_2689_, 1);
lean_inc_ref(v_binderType_2697_);
v_body_2698_ = lean_ctor_get(v_e_2689_, 2);
lean_inc_ref(v_body_2698_);
v_binderInfo_2699_ = lean_ctor_get_uint8(v_e_2689_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_2689_);
v___x_2700_ = lean_expr_instantiate_rev(v_binderType_2697_, v_fvars_2688_);
lean_dec_ref(v_binderType_2697_);
lean_inc(v___y_2694_);
lean_inc_ref(v___y_2693_);
lean_inc(v___y_2692_);
lean_inc_ref(v___y_2691_);
lean_inc(v_a_2690_);
lean_inc_ref(v_post_2684_);
lean_inc_ref(v_pre_2683_);
v___x_2701_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2683_, v_post_2684_, v_usedLetOnly_2685_, v_skipConstInApp_2686_, v_skipInstances_2687_, v___x_2700_, v_a_2690_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_);
if (lean_obj_tag(v___x_2701_) == 0)
{
lean_object* v_a_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___f_2706_; uint8_t v___x_2707_; lean_object* v___x_2708_; 
v_a_2702_ = lean_ctor_get(v___x_2701_, 0);
lean_inc(v_a_2702_);
lean_dec_ref(v___x_2701_);
v___x_2703_ = lean_box(v_usedLetOnly_2685_);
v___x_2704_ = lean_box(v_skipConstInApp_2686_);
v___x_2705_ = lean_box(v_skipInstances_2687_);
v___f_2706_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9___lam__0___boxed), 14, 7);
lean_closure_set(v___f_2706_, 0, v_fvars_2688_);
lean_closure_set(v___f_2706_, 1, v_pre_2683_);
lean_closure_set(v___f_2706_, 2, v_post_2684_);
lean_closure_set(v___f_2706_, 3, v___x_2703_);
lean_closure_set(v___f_2706_, 4, v___x_2704_);
lean_closure_set(v___f_2706_, 5, v___x_2705_);
lean_closure_set(v___f_2706_, 6, v_body_2698_);
v___x_2707_ = 0;
v___x_2708_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg(v_binderName_2696_, v_binderInfo_2699_, v_a_2702_, v___f_2706_, v___x_2707_, v_a_2690_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_);
return v___x_2708_;
}
else
{
lean_dec_ref(v_body_2698_);
lean_dec(v_binderName_2696_);
lean_dec(v___y_2694_);
lean_dec_ref(v___y_2693_);
lean_dec(v___y_2692_);
lean_dec_ref(v___y_2691_);
lean_dec(v_a_2690_);
lean_dec_ref(v_fvars_2688_);
lean_dec_ref(v_post_2684_);
lean_dec_ref(v_pre_2683_);
return v___x_2701_;
}
}
else
{
lean_object* v___x_2709_; lean_object* v___x_2710_; 
v___x_2709_ = lean_expr_instantiate_rev(v_e_2689_, v_fvars_2688_);
lean_dec_ref(v_e_2689_);
lean_inc(v___y_2694_);
lean_inc_ref(v___y_2693_);
lean_inc(v___y_2692_);
lean_inc_ref(v___y_2691_);
lean_inc(v_a_2690_);
lean_inc_ref(v_post_2684_);
lean_inc_ref(v_pre_2683_);
v___x_2710_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2683_, v_post_2684_, v_usedLetOnly_2685_, v_skipConstInApp_2686_, v_skipInstances_2687_, v___x_2709_, v_a_2690_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_);
if (lean_obj_tag(v___x_2710_) == 0)
{
lean_object* v_a_2711_; uint8_t v___x_2712_; uint8_t v___x_2713_; uint8_t v___x_2714_; lean_object* v___x_2715_; 
v_a_2711_ = lean_ctor_get(v___x_2710_, 0);
lean_inc(v_a_2711_);
lean_dec_ref(v___x_2710_);
v___x_2712_ = 0;
v___x_2713_ = 1;
v___x_2714_ = 1;
v___x_2715_ = l_Lean_Meta_mkLambdaFVars(v_fvars_2688_, v_a_2711_, v___x_2712_, v_usedLetOnly_2685_, v___x_2712_, v___x_2713_, v___x_2714_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_);
lean_dec_ref(v_fvars_2688_);
if (lean_obj_tag(v___x_2715_) == 0)
{
lean_object* v_a_2716_; lean_object* v___x_2717_; 
v_a_2716_ = lean_ctor_get(v___x_2715_, 0);
lean_inc(v_a_2716_);
lean_dec_ref(v___x_2715_);
v___x_2717_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_2683_, v_post_2684_, v_usedLetOnly_2685_, v_skipConstInApp_2686_, v_skipInstances_2687_, v_a_2716_, v_a_2690_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_);
return v___x_2717_;
}
else
{
lean_dec(v___y_2694_);
lean_dec_ref(v___y_2693_);
lean_dec(v___y_2692_);
lean_dec_ref(v___y_2691_);
lean_dec(v_a_2690_);
lean_dec_ref(v_post_2684_);
lean_dec_ref(v_pre_2683_);
return v___x_2715_;
}
}
else
{
lean_dec(v___y_2694_);
lean_dec_ref(v___y_2693_);
lean_dec(v___y_2692_);
lean_dec_ref(v___y_2691_);
lean_dec(v_a_2690_);
lean_dec_ref(v_fvars_2688_);
lean_dec_ref(v_post_2684_);
lean_dec_ref(v_pre_2683_);
return v___x_2710_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10___lam__0(lean_object* v_fvars_2718_, lean_object* v_pre_2719_, lean_object* v_post_2720_, uint8_t v_usedLetOnly_2721_, uint8_t v_skipConstInApp_2722_, uint8_t v_skipInstances_2723_, lean_object* v_body_2724_, lean_object* v_x_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_){
_start:
{
lean_object* v___x_2732_; lean_object* v___x_2733_; 
v___x_2732_ = lean_array_push(v_fvars_2718_, v_x_2725_);
v___x_2733_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10(v_pre_2719_, v_post_2720_, v_usedLetOnly_2721_, v_skipConstInApp_2722_, v_skipInstances_2723_, v___x_2732_, v_body_2724_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_);
return v___x_2733_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10___lam__0___boxed(lean_object* v_fvars_2734_, lean_object* v_pre_2735_, lean_object* v_post_2736_, lean_object* v_usedLetOnly_2737_, lean_object* v_skipConstInApp_2738_, lean_object* v_skipInstances_2739_, lean_object* v_body_2740_, lean_object* v_x_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_){
_start:
{
uint8_t v_usedLetOnly_boxed_2748_; uint8_t v_skipConstInApp_boxed_2749_; uint8_t v_skipInstances_boxed_2750_; lean_object* v_res_2751_; 
v_usedLetOnly_boxed_2748_ = lean_unbox(v_usedLetOnly_2737_);
v_skipConstInApp_boxed_2749_ = lean_unbox(v_skipConstInApp_2738_);
v_skipInstances_boxed_2750_ = lean_unbox(v_skipInstances_2739_);
v_res_2751_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10___lam__0(v_fvars_2734_, v_pre_2735_, v_post_2736_, v_usedLetOnly_boxed_2748_, v_skipConstInApp_boxed_2749_, v_skipInstances_boxed_2750_, v_body_2740_, v_x_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_);
return v_res_2751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10(lean_object* v_pre_2752_, lean_object* v_post_2753_, uint8_t v_usedLetOnly_2754_, uint8_t v_skipConstInApp_2755_, uint8_t v_skipInstances_2756_, lean_object* v_fvars_2757_, lean_object* v_e_2758_, lean_object* v_a_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_){
_start:
{
if (lean_obj_tag(v_e_2758_) == 8)
{
lean_object* v_declName_2765_; lean_object* v_type_2766_; lean_object* v_value_2767_; lean_object* v_body_2768_; uint8_t v_nondep_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; 
v_declName_2765_ = lean_ctor_get(v_e_2758_, 0);
lean_inc(v_declName_2765_);
v_type_2766_ = lean_ctor_get(v_e_2758_, 1);
lean_inc_ref(v_type_2766_);
v_value_2767_ = lean_ctor_get(v_e_2758_, 2);
lean_inc_ref(v_value_2767_);
v_body_2768_ = lean_ctor_get(v_e_2758_, 3);
lean_inc_ref(v_body_2768_);
v_nondep_2769_ = lean_ctor_get_uint8(v_e_2758_, sizeof(void*)*4 + 8);
lean_dec_ref(v_e_2758_);
v___x_2770_ = lean_expr_instantiate_rev(v_type_2766_, v_fvars_2757_);
lean_dec_ref(v_type_2766_);
lean_inc(v___y_2763_);
lean_inc_ref(v___y_2762_);
lean_inc(v___y_2761_);
lean_inc_ref(v___y_2760_);
lean_inc(v_a_2759_);
lean_inc_ref(v_post_2753_);
lean_inc_ref(v_pre_2752_);
v___x_2771_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2752_, v_post_2753_, v_usedLetOnly_2754_, v_skipConstInApp_2755_, v_skipInstances_2756_, v___x_2770_, v_a_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_);
if (lean_obj_tag(v___x_2771_) == 0)
{
lean_object* v_a_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; 
v_a_2772_ = lean_ctor_get(v___x_2771_, 0);
lean_inc(v_a_2772_);
lean_dec_ref(v___x_2771_);
v___x_2773_ = lean_expr_instantiate_rev(v_value_2767_, v_fvars_2757_);
lean_dec_ref(v_value_2767_);
lean_inc(v___y_2763_);
lean_inc_ref(v___y_2762_);
lean_inc(v___y_2761_);
lean_inc_ref(v___y_2760_);
lean_inc(v_a_2759_);
lean_inc_ref(v_post_2753_);
lean_inc_ref(v_pre_2752_);
v___x_2774_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2752_, v_post_2753_, v_usedLetOnly_2754_, v_skipConstInApp_2755_, v_skipInstances_2756_, v___x_2773_, v_a_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_);
if (lean_obj_tag(v___x_2774_) == 0)
{
lean_object* v_a_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___f_2779_; uint8_t v___x_2780_; lean_object* v___x_2781_; 
v_a_2775_ = lean_ctor_get(v___x_2774_, 0);
lean_inc(v_a_2775_);
lean_dec_ref(v___x_2774_);
v___x_2776_ = lean_box(v_usedLetOnly_2754_);
v___x_2777_ = lean_box(v_skipConstInApp_2755_);
v___x_2778_ = lean_box(v_skipInstances_2756_);
v___f_2779_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10___lam__0___boxed), 14, 7);
lean_closure_set(v___f_2779_, 0, v_fvars_2757_);
lean_closure_set(v___f_2779_, 1, v_pre_2752_);
lean_closure_set(v___f_2779_, 2, v_post_2753_);
lean_closure_set(v___f_2779_, 3, v___x_2776_);
lean_closure_set(v___f_2779_, 4, v___x_2777_);
lean_closure_set(v___f_2779_, 5, v___x_2778_);
lean_closure_set(v___f_2779_, 6, v_body_2768_);
v___x_2780_ = 0;
v___x_2781_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13___redArg(v_declName_2765_, v_a_2772_, v_a_2775_, v___f_2779_, v_nondep_2769_, v___x_2780_, v_a_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_);
return v___x_2781_;
}
else
{
lean_dec(v_a_2772_);
lean_dec_ref(v_body_2768_);
lean_dec(v_declName_2765_);
lean_dec(v___y_2763_);
lean_dec_ref(v___y_2762_);
lean_dec(v___y_2761_);
lean_dec_ref(v___y_2760_);
lean_dec(v_a_2759_);
lean_dec_ref(v_fvars_2757_);
lean_dec_ref(v_post_2753_);
lean_dec_ref(v_pre_2752_);
return v___x_2774_;
}
}
else
{
lean_dec_ref(v_body_2768_);
lean_dec_ref(v_value_2767_);
lean_dec(v_declName_2765_);
lean_dec(v___y_2763_);
lean_dec_ref(v___y_2762_);
lean_dec(v___y_2761_);
lean_dec_ref(v___y_2760_);
lean_dec(v_a_2759_);
lean_dec_ref(v_fvars_2757_);
lean_dec_ref(v_post_2753_);
lean_dec_ref(v_pre_2752_);
return v___x_2771_;
}
}
else
{
lean_object* v___x_2782_; lean_object* v___x_2783_; 
v___x_2782_ = lean_expr_instantiate_rev(v_e_2758_, v_fvars_2757_);
lean_dec_ref(v_e_2758_);
lean_inc(v___y_2763_);
lean_inc_ref(v___y_2762_);
lean_inc(v___y_2761_);
lean_inc_ref(v___y_2760_);
lean_inc(v_a_2759_);
lean_inc_ref(v_post_2753_);
lean_inc_ref(v_pre_2752_);
v___x_2783_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2752_, v_post_2753_, v_usedLetOnly_2754_, v_skipConstInApp_2755_, v_skipInstances_2756_, v___x_2782_, v_a_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_);
if (lean_obj_tag(v___x_2783_) == 0)
{
lean_object* v_a_2784_; uint8_t v___x_2785_; uint8_t v___x_2786_; lean_object* v___x_2787_; 
v_a_2784_ = lean_ctor_get(v___x_2783_, 0);
lean_inc(v_a_2784_);
lean_dec_ref(v___x_2783_);
v___x_2785_ = 0;
v___x_2786_ = 1;
v___x_2787_ = l_Lean_Meta_mkLetFVars(v_fvars_2757_, v_a_2784_, v_usedLetOnly_2754_, v___x_2785_, v___x_2786_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_);
lean_dec_ref(v_fvars_2757_);
if (lean_obj_tag(v___x_2787_) == 0)
{
lean_object* v_a_2788_; lean_object* v___x_2789_; 
v_a_2788_ = lean_ctor_get(v___x_2787_, 0);
lean_inc(v_a_2788_);
lean_dec_ref(v___x_2787_);
v___x_2789_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_2752_, v_post_2753_, v_usedLetOnly_2754_, v_skipConstInApp_2755_, v_skipInstances_2756_, v_a_2788_, v_a_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_);
return v___x_2789_;
}
else
{
lean_dec(v___y_2763_);
lean_dec_ref(v___y_2762_);
lean_dec(v___y_2761_);
lean_dec_ref(v___y_2760_);
lean_dec(v_a_2759_);
lean_dec_ref(v_post_2753_);
lean_dec_ref(v_pre_2752_);
return v___x_2787_;
}
}
else
{
lean_dec(v___y_2763_);
lean_dec_ref(v___y_2762_);
lean_dec(v___y_2761_);
lean_dec_ref(v___y_2760_);
lean_dec(v_a_2759_);
lean_dec_ref(v_fvars_2757_);
lean_dec_ref(v_post_2753_);
lean_dec_ref(v_pre_2752_);
return v___x_2783_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__4(lean_object* v_pre_2790_, lean_object* v_post_2791_, uint8_t v_usedLetOnly_2792_, uint8_t v_skipConstInApp_2793_, uint8_t v_skipInstances_2794_, size_t v_sz_2795_, size_t v_i_2796_, lean_object* v_bs_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_){
_start:
{
uint8_t v___x_2804_; 
v___x_2804_ = lean_usize_dec_lt(v_i_2796_, v_sz_2795_);
if (v___x_2804_ == 0)
{
lean_object* v___x_2805_; 
lean_dec(v___y_2802_);
lean_dec_ref(v___y_2801_);
lean_dec(v___y_2800_);
lean_dec_ref(v___y_2799_);
lean_dec(v___y_2798_);
lean_dec_ref(v_post_2791_);
lean_dec_ref(v_pre_2790_);
v___x_2805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2805_, 0, v_bs_2797_);
return v___x_2805_;
}
else
{
lean_object* v_v_2806_; lean_object* v___x_2807_; 
v_v_2806_ = lean_array_uget_borrowed(v_bs_2797_, v_i_2796_);
lean_inc(v___y_2802_);
lean_inc_ref(v___y_2801_);
lean_inc(v___y_2800_);
lean_inc_ref(v___y_2799_);
lean_inc(v___y_2798_);
lean_inc(v_v_2806_);
lean_inc_ref(v_post_2791_);
lean_inc_ref(v_pre_2790_);
v___x_2807_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2790_, v_post_2791_, v_usedLetOnly_2792_, v_skipConstInApp_2793_, v_skipInstances_2794_, v_v_2806_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_);
if (lean_obj_tag(v___x_2807_) == 0)
{
lean_object* v_a_2808_; lean_object* v___x_2809_; lean_object* v_bs_x27_2810_; size_t v___x_2811_; size_t v___x_2812_; lean_object* v___x_2813_; 
v_a_2808_ = lean_ctor_get(v___x_2807_, 0);
lean_inc(v_a_2808_);
lean_dec_ref(v___x_2807_);
v___x_2809_ = lean_unsigned_to_nat(0u);
v_bs_x27_2810_ = lean_array_uset(v_bs_2797_, v_i_2796_, v___x_2809_);
v___x_2811_ = ((size_t)1ULL);
v___x_2812_ = lean_usize_add(v_i_2796_, v___x_2811_);
v___x_2813_ = lean_array_uset(v_bs_x27_2810_, v_i_2796_, v_a_2808_);
v_i_2796_ = v___x_2812_;
v_bs_2797_ = v___x_2813_;
goto _start;
}
else
{
lean_object* v_a_2815_; lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2822_; 
lean_dec(v___y_2802_);
lean_dec_ref(v___y_2801_);
lean_dec(v___y_2800_);
lean_dec_ref(v___y_2799_);
lean_dec(v___y_2798_);
lean_dec_ref(v_bs_2797_);
lean_dec_ref(v_post_2791_);
lean_dec_ref(v_pre_2790_);
v_a_2815_ = lean_ctor_get(v___x_2807_, 0);
v_isSharedCheck_2822_ = !lean_is_exclusive(v___x_2807_);
if (v_isSharedCheck_2822_ == 0)
{
v___x_2817_ = v___x_2807_;
v_isShared_2818_ = v_isSharedCheck_2822_;
goto v_resetjp_2816_;
}
else
{
lean_inc(v_a_2815_);
lean_dec(v___x_2807_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2822_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
lean_object* v___x_2820_; 
if (v_isShared_2818_ == 0)
{
v___x_2820_ = v___x_2817_;
goto v_reusejp_2819_;
}
else
{
lean_object* v_reuseFailAlloc_2821_; 
v_reuseFailAlloc_2821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2821_, 0, v_a_2815_);
v___x_2820_ = v_reuseFailAlloc_2821_;
goto v_reusejp_2819_;
}
v_reusejp_2819_:
{
return v___x_2820_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___lam__0(lean_object* v_pre_2823_, lean_object* v_post_2824_, uint8_t v_usedLetOnly_2825_, uint8_t v_skipConstInApp_2826_, uint8_t v_skipInstances_2827_, lean_object* v___x_2828_, lean_object* v___y_2829_, lean_object* v_b_2830_, lean_object* v_a_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_){
_start:
{
lean_object* v___x_2837_; 
v___x_2837_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2823_, v_post_2824_, v_usedLetOnly_2825_, v_skipConstInApp_2826_, v_skipInstances_2827_, v___x_2828_, v___y_2829_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_);
if (lean_obj_tag(v___x_2837_) == 0)
{
lean_object* v_a_2838_; lean_object* v___x_2840_; uint8_t v_isShared_2841_; uint8_t v_isSharedCheck_2847_; 
v_a_2838_ = lean_ctor_get(v___x_2837_, 0);
v_isSharedCheck_2847_ = !lean_is_exclusive(v___x_2837_);
if (v_isSharedCheck_2847_ == 0)
{
v___x_2840_ = v___x_2837_;
v_isShared_2841_ = v_isSharedCheck_2847_;
goto v_resetjp_2839_;
}
else
{
lean_inc(v_a_2838_);
lean_dec(v___x_2837_);
v___x_2840_ = lean_box(0);
v_isShared_2841_ = v_isSharedCheck_2847_;
goto v_resetjp_2839_;
}
v_resetjp_2839_:
{
lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2845_; 
v___x_2842_ = lean_array_fset(v_b_2830_, v_a_2831_, v_a_2838_);
v___x_2843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2843_, 0, v___x_2842_);
if (v_isShared_2841_ == 0)
{
lean_ctor_set(v___x_2840_, 0, v___x_2843_);
v___x_2845_ = v___x_2840_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2846_; 
v_reuseFailAlloc_2846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2846_, 0, v___x_2843_);
v___x_2845_ = v_reuseFailAlloc_2846_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
return v___x_2845_;
}
}
}
else
{
lean_object* v_a_2848_; lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_2855_; 
lean_dec_ref(v_b_2830_);
v_a_2848_ = lean_ctor_get(v___x_2837_, 0);
v_isSharedCheck_2855_ = !lean_is_exclusive(v___x_2837_);
if (v_isSharedCheck_2855_ == 0)
{
v___x_2850_ = v___x_2837_;
v_isShared_2851_ = v_isSharedCheck_2855_;
goto v_resetjp_2849_;
}
else
{
lean_inc(v_a_2848_);
lean_dec(v___x_2837_);
v___x_2850_ = lean_box(0);
v_isShared_2851_ = v_isSharedCheck_2855_;
goto v_resetjp_2849_;
}
v_resetjp_2849_:
{
lean_object* v___x_2853_; 
if (v_isShared_2851_ == 0)
{
v___x_2853_ = v___x_2850_;
goto v_reusejp_2852_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v_a_2848_);
v___x_2853_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2852_;
}
v_reusejp_2852_:
{
return v___x_2853_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___lam__0___boxed(lean_object* v_pre_2856_, lean_object* v_post_2857_, lean_object* v_usedLetOnly_2858_, lean_object* v_skipConstInApp_2859_, lean_object* v_skipInstances_2860_, lean_object* v___x_2861_, lean_object* v___y_2862_, lean_object* v_b_2863_, lean_object* v_a_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_){
_start:
{
uint8_t v_usedLetOnly_boxed_2870_; uint8_t v_skipConstInApp_boxed_2871_; uint8_t v_skipInstances_boxed_2872_; lean_object* v_res_2873_; 
v_usedLetOnly_boxed_2870_ = lean_unbox(v_usedLetOnly_2858_);
v_skipConstInApp_boxed_2871_ = lean_unbox(v_skipConstInApp_2859_);
v_skipInstances_boxed_2872_ = lean_unbox(v_skipInstances_2860_);
v_res_2873_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___lam__0(v_pre_2856_, v_post_2857_, v_usedLetOnly_boxed_2870_, v_skipConstInApp_boxed_2871_, v_skipInstances_boxed_2872_, v___x_2861_, v___y_2862_, v_b_2863_, v_a_2864_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_);
lean_dec(v_a_2864_);
return v_res_2873_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg(lean_object* v_upperBound_2874_, lean_object* v___x_2875_, lean_object* v_pre_2876_, lean_object* v_post_2877_, uint8_t v_usedLetOnly_2878_, uint8_t v_skipConstInApp_2879_, uint8_t v_skipInstances_2880_, lean_object* v_a_2881_, lean_object* v_b_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_){
_start:
{
lean_object* v___y_2890_; uint8_t v___x_2913_; 
v___x_2913_ = lean_nat_dec_lt(v_a_2881_, v_upperBound_2874_);
if (v___x_2913_ == 0)
{
lean_object* v___x_2914_; 
lean_dec(v___y_2887_);
lean_dec_ref(v___y_2886_);
lean_dec(v___y_2885_);
lean_dec_ref(v___y_2884_);
lean_dec(v___y_2883_);
lean_dec(v_a_2881_);
lean_dec_ref(v_post_2877_);
lean_dec_ref(v_pre_2876_);
v___x_2914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2914_, 0, v_b_2882_);
return v___x_2914_;
}
else
{
lean_object* v___x_2915_; lean_object* v___x_2916_; uint8_t v___x_2917_; 
v___x_2915_ = lean_array_fget_borrowed(v_b_2882_, v_a_2881_);
v___x_2916_ = lean_array_get_size(v___x_2875_);
v___x_2917_ = lean_nat_dec_lt(v_a_2881_, v___x_2916_);
if (v___x_2917_ == 0)
{
lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___f_2921_; 
lean_inc(v___x_2915_);
v___x_2918_ = lean_box(v_usedLetOnly_2878_);
v___x_2919_ = lean_box(v_skipConstInApp_2879_);
v___x_2920_ = lean_box(v_skipInstances_2880_);
lean_inc(v_a_2881_);
lean_inc(v___y_2883_);
lean_inc_ref(v_post_2877_);
lean_inc_ref(v_pre_2876_);
v___f_2921_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_2921_, 0, v_pre_2876_);
lean_closure_set(v___f_2921_, 1, v_post_2877_);
lean_closure_set(v___f_2921_, 2, v___x_2918_);
lean_closure_set(v___f_2921_, 3, v___x_2919_);
lean_closure_set(v___f_2921_, 4, v___x_2920_);
lean_closure_set(v___f_2921_, 5, v___x_2915_);
lean_closure_set(v___f_2921_, 6, v___y_2883_);
lean_closure_set(v___f_2921_, 7, v_b_2882_);
lean_closure_set(v___f_2921_, 8, v_a_2881_);
v___y_2890_ = v___f_2921_;
goto v___jp_2889_;
}
else
{
lean_object* v___x_2922_; uint8_t v_isInstance_2923_; 
v___x_2922_ = lean_array_fget_borrowed(v___x_2875_, v_a_2881_);
v_isInstance_2923_ = lean_ctor_get_uint8(v___x_2922_, sizeof(void*)*1 + 4);
if (v_isInstance_2923_ == 0)
{
lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___f_2927_; 
lean_inc(v___x_2915_);
v___x_2924_ = lean_box(v_usedLetOnly_2878_);
v___x_2925_ = lean_box(v_skipConstInApp_2879_);
v___x_2926_ = lean_box(v_skipInstances_2880_);
lean_inc(v_a_2881_);
lean_inc(v___y_2883_);
lean_inc_ref(v_post_2877_);
lean_inc_ref(v_pre_2876_);
v___f_2927_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_2927_, 0, v_pre_2876_);
lean_closure_set(v___f_2927_, 1, v_post_2877_);
lean_closure_set(v___f_2927_, 2, v___x_2924_);
lean_closure_set(v___f_2927_, 3, v___x_2925_);
lean_closure_set(v___f_2927_, 4, v___x_2926_);
lean_closure_set(v___f_2927_, 5, v___x_2915_);
lean_closure_set(v___f_2927_, 6, v___y_2883_);
lean_closure_set(v___f_2927_, 7, v_b_2882_);
lean_closure_set(v___f_2927_, 8, v_a_2881_);
v___y_2890_ = v___f_2927_;
goto v___jp_2889_;
}
else
{
lean_object* v___x_2928_; lean_object* v___f_2929_; 
v___x_2928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2928_, 0, v_b_2882_);
v___f_2929_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_2929_, 0, v___x_2928_);
v___y_2890_ = v___f_2929_;
goto v___jp_2889_;
}
}
}
v___jp_2889_:
{
lean_object* v___x_2891_; 
lean_inc(v___y_2887_);
lean_inc_ref(v___y_2886_);
lean_inc(v___y_2885_);
lean_inc_ref(v___y_2884_);
v___x_2891_ = lean_apply_5(v___y_2890_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_, lean_box(0));
if (lean_obj_tag(v___x_2891_) == 0)
{
lean_object* v_a_2892_; lean_object* v___x_2894_; uint8_t v_isShared_2895_; uint8_t v_isSharedCheck_2904_; 
v_a_2892_ = lean_ctor_get(v___x_2891_, 0);
v_isSharedCheck_2904_ = !lean_is_exclusive(v___x_2891_);
if (v_isSharedCheck_2904_ == 0)
{
v___x_2894_ = v___x_2891_;
v_isShared_2895_ = v_isSharedCheck_2904_;
goto v_resetjp_2893_;
}
else
{
lean_inc(v_a_2892_);
lean_dec(v___x_2891_);
v___x_2894_ = lean_box(0);
v_isShared_2895_ = v_isSharedCheck_2904_;
goto v_resetjp_2893_;
}
v_resetjp_2893_:
{
if (lean_obj_tag(v_a_2892_) == 0)
{
lean_object* v_a_2896_; lean_object* v___x_2898_; 
lean_dec(v___y_2887_);
lean_dec_ref(v___y_2886_);
lean_dec(v___y_2885_);
lean_dec_ref(v___y_2884_);
lean_dec(v___y_2883_);
lean_dec(v_a_2881_);
lean_dec_ref(v_post_2877_);
lean_dec_ref(v_pre_2876_);
v_a_2896_ = lean_ctor_get(v_a_2892_, 0);
lean_inc(v_a_2896_);
lean_dec_ref(v_a_2892_);
if (v_isShared_2895_ == 0)
{
lean_ctor_set(v___x_2894_, 0, v_a_2896_);
v___x_2898_ = v___x_2894_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2899_; 
v_reuseFailAlloc_2899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2899_, 0, v_a_2896_);
v___x_2898_ = v_reuseFailAlloc_2899_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
return v___x_2898_;
}
}
else
{
lean_object* v_a_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; 
lean_del_object(v___x_2894_);
v_a_2900_ = lean_ctor_get(v_a_2892_, 0);
lean_inc(v_a_2900_);
lean_dec_ref(v_a_2892_);
v___x_2901_ = lean_unsigned_to_nat(1u);
v___x_2902_ = lean_nat_add(v_a_2881_, v___x_2901_);
lean_dec(v_a_2881_);
v_a_2881_ = v___x_2902_;
v_b_2882_ = v_a_2900_;
goto _start;
}
}
}
else
{
lean_object* v_a_2905_; lean_object* v___x_2907_; uint8_t v_isShared_2908_; uint8_t v_isSharedCheck_2912_; 
lean_dec(v___y_2887_);
lean_dec_ref(v___y_2886_);
lean_dec(v___y_2885_);
lean_dec_ref(v___y_2884_);
lean_dec(v___y_2883_);
lean_dec(v_a_2881_);
lean_dec_ref(v_post_2877_);
lean_dec_ref(v_pre_2876_);
v_a_2905_ = lean_ctor_get(v___x_2891_, 0);
v_isSharedCheck_2912_ = !lean_is_exclusive(v___x_2891_);
if (v_isSharedCheck_2912_ == 0)
{
v___x_2907_ = v___x_2891_;
v_isShared_2908_ = v_isSharedCheck_2912_;
goto v_resetjp_2906_;
}
else
{
lean_inc(v_a_2905_);
lean_dec(v___x_2891_);
v___x_2907_ = lean_box(0);
v_isShared_2908_ = v_isSharedCheck_2912_;
goto v_resetjp_2906_;
}
v_resetjp_2906_:
{
lean_object* v___x_2910_; 
if (v_isShared_2908_ == 0)
{
v___x_2910_ = v___x_2907_;
goto v_reusejp_2909_;
}
else
{
lean_object* v_reuseFailAlloc_2911_; 
v_reuseFailAlloc_2911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2911_, 0, v_a_2905_);
v___x_2910_ = v_reuseFailAlloc_2911_;
goto v_reusejp_2909_;
}
v_reusejp_2909_:
{
return v___x_2910_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__11(uint8_t v_skipInstances_2930_, lean_object* v_pre_2931_, lean_object* v_post_2932_, uint8_t v_usedLetOnly_2933_, uint8_t v_skipConstInApp_2934_, lean_object* v_x_2935_, lean_object* v_x_2936_, lean_object* v_x_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_){
_start:
{
lean_object* v_f_2945_; lean_object* v___y_2946_; lean_object* v___y_2947_; lean_object* v___y_2948_; lean_object* v___y_2949_; lean_object* v___y_2950_; 
if (lean_obj_tag(v_x_2935_) == 5)
{
lean_object* v_fn_2993_; lean_object* v_arg_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; 
v_fn_2993_ = lean_ctor_get(v_x_2935_, 0);
lean_inc_ref(v_fn_2993_);
v_arg_2994_ = lean_ctor_get(v_x_2935_, 1);
lean_inc_ref(v_arg_2994_);
lean_dec_ref(v_x_2935_);
v___x_2995_ = lean_array_set(v_x_2936_, v_x_2937_, v_arg_2994_);
v___x_2996_ = lean_unsigned_to_nat(1u);
v___x_2997_ = lean_nat_sub(v_x_2937_, v___x_2996_);
lean_dec(v_x_2937_);
v_x_2935_ = v_fn_2993_;
v_x_2936_ = v___x_2995_;
v_x_2937_ = v___x_2997_;
goto _start;
}
else
{
lean_dec(v_x_2937_);
if (v_skipConstInApp_2934_ == 0)
{
goto v___jp_2990_;
}
else
{
uint8_t v___x_2999_; 
v___x_2999_ = l_Lean_Expr_isConst(v_x_2935_);
if (v___x_2999_ == 0)
{
goto v___jp_2990_;
}
else
{
v_f_2945_ = v_x_2935_;
v___y_2946_ = v___y_2938_;
v___y_2947_ = v___y_2939_;
v___y_2948_ = v___y_2940_;
v___y_2949_ = v___y_2941_;
v___y_2950_ = v___y_2942_;
goto v___jp_2944_;
}
}
}
v___jp_2944_:
{
if (v_skipInstances_2930_ == 0)
{
size_t v_sz_2951_; size_t v___x_2952_; lean_object* v___x_2953_; 
v_sz_2951_ = lean_array_size(v_x_2936_);
v___x_2952_ = ((size_t)0ULL);
lean_inc(v___y_2950_);
lean_inc_ref(v___y_2949_);
lean_inc(v___y_2948_);
lean_inc_ref(v___y_2947_);
lean_inc(v___y_2946_);
lean_inc_ref(v_post_2932_);
lean_inc_ref(v_pre_2931_);
v___x_2953_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__4(v_pre_2931_, v_post_2932_, v_usedLetOnly_2933_, v_skipConstInApp_2934_, v_skipInstances_2930_, v_sz_2951_, v___x_2952_, v_x_2936_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_);
if (lean_obj_tag(v___x_2953_) == 0)
{
lean_object* v_a_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; 
v_a_2954_ = lean_ctor_get(v___x_2953_, 0);
lean_inc(v_a_2954_);
lean_dec_ref(v___x_2953_);
v___x_2955_ = l_Lean_mkAppN(v_f_2945_, v_a_2954_);
lean_dec(v_a_2954_);
v___x_2956_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_2931_, v_post_2932_, v_usedLetOnly_2933_, v_skipConstInApp_2934_, v_skipInstances_2930_, v___x_2955_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_);
return v___x_2956_;
}
else
{
lean_object* v_a_2957_; lean_object* v___x_2959_; uint8_t v_isShared_2960_; uint8_t v_isSharedCheck_2964_; 
lean_dec(v___y_2950_);
lean_dec_ref(v___y_2949_);
lean_dec(v___y_2948_);
lean_dec_ref(v___y_2947_);
lean_dec(v___y_2946_);
lean_dec_ref(v_f_2945_);
lean_dec_ref(v_post_2932_);
lean_dec_ref(v_pre_2931_);
v_a_2957_ = lean_ctor_get(v___x_2953_, 0);
v_isSharedCheck_2964_ = !lean_is_exclusive(v___x_2953_);
if (v_isSharedCheck_2964_ == 0)
{
v___x_2959_ = v___x_2953_;
v_isShared_2960_ = v_isSharedCheck_2964_;
goto v_resetjp_2958_;
}
else
{
lean_inc(v_a_2957_);
lean_dec(v___x_2953_);
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
else
{
lean_object* v___x_2965_; lean_object* v___x_2966_; 
v___x_2965_ = lean_array_get_size(v_x_2936_);
lean_inc(v___y_2950_);
lean_inc_ref(v___y_2949_);
lean_inc(v___y_2948_);
lean_inc_ref(v___y_2947_);
lean_inc_ref(v_f_2945_);
v___x_2966_ = l_Lean_Meta_getFunInfoNArgs(v_f_2945_, v___x_2965_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_);
if (lean_obj_tag(v___x_2966_) == 0)
{
lean_object* v_a_2967_; lean_object* v_paramInfo_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; 
v_a_2967_ = lean_ctor_get(v___x_2966_, 0);
lean_inc(v_a_2967_);
lean_dec_ref(v___x_2966_);
v_paramInfo_2968_ = lean_ctor_get(v_a_2967_, 0);
lean_inc_ref(v_paramInfo_2968_);
lean_dec(v_a_2967_);
v___x_2969_ = lean_unsigned_to_nat(0u);
lean_inc(v___y_2950_);
lean_inc_ref(v___y_2949_);
lean_inc(v___y_2948_);
lean_inc_ref(v___y_2947_);
lean_inc(v___y_2946_);
lean_inc_ref(v_post_2932_);
lean_inc_ref(v_pre_2931_);
v___x_2970_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg(v___x_2965_, v_paramInfo_2968_, v_pre_2931_, v_post_2932_, v_usedLetOnly_2933_, v_skipConstInApp_2934_, v_skipInstances_2930_, v___x_2969_, v_x_2936_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_);
lean_dec_ref(v_paramInfo_2968_);
if (lean_obj_tag(v___x_2970_) == 0)
{
lean_object* v_a_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; 
v_a_2971_ = lean_ctor_get(v___x_2970_, 0);
lean_inc(v_a_2971_);
lean_dec_ref(v___x_2970_);
v___x_2972_ = l_Lean_mkAppN(v_f_2945_, v_a_2971_);
lean_dec(v_a_2971_);
v___x_2973_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_2931_, v_post_2932_, v_usedLetOnly_2933_, v_skipConstInApp_2934_, v_skipInstances_2930_, v___x_2972_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_);
return v___x_2973_;
}
else
{
lean_object* v_a_2974_; lean_object* v___x_2976_; uint8_t v_isShared_2977_; uint8_t v_isSharedCheck_2981_; 
lean_dec(v___y_2950_);
lean_dec_ref(v___y_2949_);
lean_dec(v___y_2948_);
lean_dec_ref(v___y_2947_);
lean_dec(v___y_2946_);
lean_dec_ref(v_f_2945_);
lean_dec_ref(v_post_2932_);
lean_dec_ref(v_pre_2931_);
v_a_2974_ = lean_ctor_get(v___x_2970_, 0);
v_isSharedCheck_2981_ = !lean_is_exclusive(v___x_2970_);
if (v_isSharedCheck_2981_ == 0)
{
v___x_2976_ = v___x_2970_;
v_isShared_2977_ = v_isSharedCheck_2981_;
goto v_resetjp_2975_;
}
else
{
lean_inc(v_a_2974_);
lean_dec(v___x_2970_);
v___x_2976_ = lean_box(0);
v_isShared_2977_ = v_isSharedCheck_2981_;
goto v_resetjp_2975_;
}
v_resetjp_2975_:
{
lean_object* v___x_2979_; 
if (v_isShared_2977_ == 0)
{
v___x_2979_ = v___x_2976_;
goto v_reusejp_2978_;
}
else
{
lean_object* v_reuseFailAlloc_2980_; 
v_reuseFailAlloc_2980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2980_, 0, v_a_2974_);
v___x_2979_ = v_reuseFailAlloc_2980_;
goto v_reusejp_2978_;
}
v_reusejp_2978_:
{
return v___x_2979_;
}
}
}
}
else
{
lean_object* v_a_2982_; lean_object* v___x_2984_; uint8_t v_isShared_2985_; uint8_t v_isSharedCheck_2989_; 
lean_dec(v___y_2950_);
lean_dec_ref(v___y_2949_);
lean_dec(v___y_2948_);
lean_dec_ref(v___y_2947_);
lean_dec(v___y_2946_);
lean_dec_ref(v_f_2945_);
lean_dec_ref(v_x_2936_);
lean_dec_ref(v_post_2932_);
lean_dec_ref(v_pre_2931_);
v_a_2982_ = lean_ctor_get(v___x_2966_, 0);
v_isSharedCheck_2989_ = !lean_is_exclusive(v___x_2966_);
if (v_isSharedCheck_2989_ == 0)
{
v___x_2984_ = v___x_2966_;
v_isShared_2985_ = v_isSharedCheck_2989_;
goto v_resetjp_2983_;
}
else
{
lean_inc(v_a_2982_);
lean_dec(v___x_2966_);
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
}
v___jp_2990_:
{
lean_object* v___x_2991_; 
lean_inc(v___y_2942_);
lean_inc_ref(v___y_2941_);
lean_inc(v___y_2940_);
lean_inc_ref(v___y_2939_);
lean_inc(v___y_2938_);
lean_inc_ref(v_post_2932_);
lean_inc_ref(v_pre_2931_);
v___x_2991_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2931_, v_post_2932_, v_usedLetOnly_2933_, v_skipConstInApp_2934_, v_skipInstances_2930_, v_x_2935_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_, v___y_2942_);
if (lean_obj_tag(v___x_2991_) == 0)
{
lean_object* v_a_2992_; 
v_a_2992_ = lean_ctor_get(v___x_2991_, 0);
lean_inc(v_a_2992_);
lean_dec_ref(v___x_2991_);
v_f_2945_ = v_a_2992_;
v___y_2946_ = v___y_2938_;
v___y_2947_ = v___y_2939_;
v___y_2948_ = v___y_2940_;
v___y_2949_ = v___y_2941_;
v___y_2950_ = v___y_2942_;
goto v___jp_2944_;
}
else
{
lean_dec(v___y_2942_);
lean_dec_ref(v___y_2941_);
lean_dec(v___y_2940_);
lean_dec_ref(v___y_2939_);
lean_dec(v___y_2938_);
lean_dec_ref(v_x_2936_);
lean_dec_ref(v_post_2932_);
lean_dec_ref(v_pre_2931_);
return v___x_2991_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__1(lean_object* v_pre_3000_, lean_object* v_e_3001_, lean_object* v_post_3002_, uint8_t v_usedLetOnly_3003_, uint8_t v_skipConstInApp_3004_, uint8_t v_skipInstances_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_){
_start:
{
lean_object* v___x_3012_; 
lean_inc_ref(v_pre_3000_);
lean_inc(v___y_3010_);
lean_inc_ref(v___y_3009_);
lean_inc(v___y_3008_);
lean_inc_ref(v___y_3007_);
lean_inc_ref(v_e_3001_);
v___x_3012_ = lean_apply_6(v_pre_3000_, v_e_3001_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_, lean_box(0));
if (lean_obj_tag(v___x_3012_) == 0)
{
lean_object* v_a_3013_; lean_object* v___x_3015_; uint8_t v_isShared_3016_; uint8_t v_isSharedCheck_3061_; 
v_a_3013_ = lean_ctor_get(v___x_3012_, 0);
v_isSharedCheck_3061_ = !lean_is_exclusive(v___x_3012_);
if (v_isSharedCheck_3061_ == 0)
{
v___x_3015_ = v___x_3012_;
v_isShared_3016_ = v_isSharedCheck_3061_;
goto v_resetjp_3014_;
}
else
{
lean_inc(v_a_3013_);
lean_dec(v___x_3012_);
v___x_3015_ = lean_box(0);
v_isShared_3016_ = v_isSharedCheck_3061_;
goto v_resetjp_3014_;
}
v_resetjp_3014_:
{
lean_object* v___y_3018_; 
switch(lean_obj_tag(v_a_3013_))
{
case 0:
{
lean_object* v_e_3053_; lean_object* v___x_3055_; 
lean_dec(v___y_3010_);
lean_dec_ref(v___y_3009_);
lean_dec(v___y_3008_);
lean_dec_ref(v___y_3007_);
lean_dec(v___y_3006_);
lean_dec_ref(v_post_3002_);
lean_dec_ref(v_e_3001_);
lean_dec_ref(v_pre_3000_);
v_e_3053_ = lean_ctor_get(v_a_3013_, 0);
lean_inc_ref(v_e_3053_);
lean_dec_ref(v_a_3013_);
if (v_isShared_3016_ == 0)
{
lean_ctor_set(v___x_3015_, 0, v_e_3053_);
v___x_3055_ = v___x_3015_;
goto v_reusejp_3054_;
}
else
{
lean_object* v_reuseFailAlloc_3056_; 
v_reuseFailAlloc_3056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3056_, 0, v_e_3053_);
v___x_3055_ = v_reuseFailAlloc_3056_;
goto v_reusejp_3054_;
}
v_reusejp_3054_:
{
return v___x_3055_;
}
}
case 1:
{
lean_object* v_e_3057_; lean_object* v___x_3058_; 
lean_del_object(v___x_3015_);
lean_dec_ref(v_e_3001_);
v_e_3057_ = lean_ctor_get(v_a_3013_, 0);
lean_inc_ref(v_e_3057_);
lean_dec_ref(v_a_3013_);
v___x_3058_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_3000_, v_post_3002_, v_usedLetOnly_3003_, v_skipConstInApp_3004_, v_skipInstances_3005_, v_e_3057_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_);
return v___x_3058_;
}
default: 
{
lean_object* v_e_x3f_3059_; 
lean_del_object(v___x_3015_);
v_e_x3f_3059_ = lean_ctor_get(v_a_3013_, 0);
lean_inc(v_e_x3f_3059_);
lean_dec_ref(v_a_3013_);
if (lean_obj_tag(v_e_x3f_3059_) == 0)
{
v___y_3018_ = v_e_3001_;
goto v___jp_3017_;
}
else
{
lean_object* v_val_3060_; 
lean_dec_ref(v_e_3001_);
v_val_3060_ = lean_ctor_get(v_e_x3f_3059_, 0);
lean_inc(v_val_3060_);
lean_dec_ref(v_e_x3f_3059_);
v___y_3018_ = v_val_3060_;
goto v___jp_3017_;
}
}
}
v___jp_3017_:
{
switch(lean_obj_tag(v___y_3018_))
{
case 7:
{
lean_object* v___x_3019_; lean_object* v___x_3020_; 
v___x_3019_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__1___closed__0));
v___x_3020_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8(v_pre_3000_, v_post_3002_, v_usedLetOnly_3003_, v_skipConstInApp_3004_, v_skipInstances_3005_, v___x_3019_, v___y_3018_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_);
return v___x_3020_;
}
case 6:
{
lean_object* v___x_3021_; lean_object* v___x_3022_; 
v___x_3021_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__1___closed__0));
v___x_3022_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9(v_pre_3000_, v_post_3002_, v_usedLetOnly_3003_, v_skipConstInApp_3004_, v_skipInstances_3005_, v___x_3021_, v___y_3018_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_);
return v___x_3022_;
}
case 8:
{
lean_object* v___x_3023_; lean_object* v___x_3024_; 
v___x_3023_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__1___closed__0));
v___x_3024_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10(v_pre_3000_, v_post_3002_, v_usedLetOnly_3003_, v_skipConstInApp_3004_, v_skipInstances_3005_, v___x_3023_, v___y_3018_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_);
return v___x_3024_;
}
case 5:
{
lean_object* v_dummy_3025_; lean_object* v_nargs_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; 
v_dummy_3025_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0);
v_nargs_3026_ = l_Lean_Expr_getAppNumArgs(v___y_3018_);
lean_inc(v_nargs_3026_);
v___x_3027_ = lean_mk_array(v_nargs_3026_, v_dummy_3025_);
v___x_3028_ = lean_unsigned_to_nat(1u);
v___x_3029_ = lean_nat_sub(v_nargs_3026_, v___x_3028_);
lean_dec(v_nargs_3026_);
v___x_3030_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__11(v_skipInstances_3005_, v_pre_3000_, v_post_3002_, v_usedLetOnly_3003_, v_skipConstInApp_3004_, v___y_3018_, v___x_3027_, v___x_3029_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_);
return v___x_3030_;
}
case 10:
{
lean_object* v_data_3031_; lean_object* v_expr_3032_; lean_object* v___x_3033_; 
v_data_3031_ = lean_ctor_get(v___y_3018_, 0);
v_expr_3032_ = lean_ctor_get(v___y_3018_, 1);
lean_inc(v___y_3010_);
lean_inc_ref(v___y_3009_);
lean_inc(v___y_3008_);
lean_inc_ref(v___y_3007_);
lean_inc(v___y_3006_);
lean_inc_ref(v_expr_3032_);
lean_inc_ref(v_post_3002_);
lean_inc_ref(v_pre_3000_);
v___x_3033_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_3000_, v_post_3002_, v_usedLetOnly_3003_, v_skipConstInApp_3004_, v_skipInstances_3005_, v_expr_3032_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_);
if (lean_obj_tag(v___x_3033_) == 0)
{
lean_object* v_a_3034_; size_t v___x_3035_; size_t v___x_3036_; uint8_t v___x_3037_; 
v_a_3034_ = lean_ctor_get(v___x_3033_, 0);
lean_inc(v_a_3034_);
lean_dec_ref(v___x_3033_);
v___x_3035_ = lean_ptr_addr(v_expr_3032_);
v___x_3036_ = lean_ptr_addr(v_a_3034_);
v___x_3037_ = lean_usize_dec_eq(v___x_3035_, v___x_3036_);
if (v___x_3037_ == 0)
{
lean_object* v___x_3038_; lean_object* v___x_3039_; 
lean_inc(v_data_3031_);
lean_dec_ref(v___y_3018_);
v___x_3038_ = l_Lean_Expr_mdata___override(v_data_3031_, v_a_3034_);
v___x_3039_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_3000_, v_post_3002_, v_usedLetOnly_3003_, v_skipConstInApp_3004_, v_skipInstances_3005_, v___x_3038_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_);
return v___x_3039_;
}
else
{
lean_object* v___x_3040_; 
lean_dec(v_a_3034_);
v___x_3040_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_3000_, v_post_3002_, v_usedLetOnly_3003_, v_skipConstInApp_3004_, v_skipInstances_3005_, v___y_3018_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_);
return v___x_3040_;
}
}
else
{
lean_dec_ref(v___y_3018_);
lean_dec(v___y_3010_);
lean_dec_ref(v___y_3009_);
lean_dec(v___y_3008_);
lean_dec_ref(v___y_3007_);
lean_dec(v___y_3006_);
lean_dec_ref(v_post_3002_);
lean_dec_ref(v_pre_3000_);
return v___x_3033_;
}
}
case 11:
{
lean_object* v_typeName_3041_; lean_object* v_idx_3042_; lean_object* v_struct_3043_; lean_object* v___x_3044_; 
v_typeName_3041_ = lean_ctor_get(v___y_3018_, 0);
v_idx_3042_ = lean_ctor_get(v___y_3018_, 1);
v_struct_3043_ = lean_ctor_get(v___y_3018_, 2);
lean_inc(v___y_3010_);
lean_inc_ref(v___y_3009_);
lean_inc(v___y_3008_);
lean_inc_ref(v___y_3007_);
lean_inc(v___y_3006_);
lean_inc_ref(v_struct_3043_);
lean_inc_ref(v_post_3002_);
lean_inc_ref(v_pre_3000_);
v___x_3044_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_3000_, v_post_3002_, v_usedLetOnly_3003_, v_skipConstInApp_3004_, v_skipInstances_3005_, v_struct_3043_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_);
if (lean_obj_tag(v___x_3044_) == 0)
{
lean_object* v_a_3045_; size_t v___x_3046_; size_t v___x_3047_; uint8_t v___x_3048_; 
v_a_3045_ = lean_ctor_get(v___x_3044_, 0);
lean_inc(v_a_3045_);
lean_dec_ref(v___x_3044_);
v___x_3046_ = lean_ptr_addr(v_struct_3043_);
v___x_3047_ = lean_ptr_addr(v_a_3045_);
v___x_3048_ = lean_usize_dec_eq(v___x_3046_, v___x_3047_);
if (v___x_3048_ == 0)
{
lean_object* v___x_3049_; lean_object* v___x_3050_; 
lean_inc(v_idx_3042_);
lean_inc(v_typeName_3041_);
lean_dec_ref(v___y_3018_);
v___x_3049_ = l_Lean_Expr_proj___override(v_typeName_3041_, v_idx_3042_, v_a_3045_);
v___x_3050_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_3000_, v_post_3002_, v_usedLetOnly_3003_, v_skipConstInApp_3004_, v_skipInstances_3005_, v___x_3049_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_);
return v___x_3050_;
}
else
{
lean_object* v___x_3051_; 
lean_dec(v_a_3045_);
v___x_3051_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_3000_, v_post_3002_, v_usedLetOnly_3003_, v_skipConstInApp_3004_, v_skipInstances_3005_, v___y_3018_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_);
return v___x_3051_;
}
}
else
{
lean_dec_ref(v___y_3018_);
lean_dec(v___y_3010_);
lean_dec_ref(v___y_3009_);
lean_dec(v___y_3008_);
lean_dec_ref(v___y_3007_);
lean_dec(v___y_3006_);
lean_dec_ref(v_post_3002_);
lean_dec_ref(v_pre_3000_);
return v___x_3044_;
}
}
default: 
{
lean_object* v___x_3052_; 
v___x_3052_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_3000_, v_post_3002_, v_usedLetOnly_3003_, v_skipConstInApp_3004_, v_skipInstances_3005_, v___y_3018_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_);
return v___x_3052_;
}
}
}
}
}
else
{
lean_object* v_a_3062_; lean_object* v___x_3064_; uint8_t v_isShared_3065_; uint8_t v_isSharedCheck_3069_; 
lean_dec(v___y_3010_);
lean_dec_ref(v___y_3009_);
lean_dec(v___y_3008_);
lean_dec_ref(v___y_3007_);
lean_dec(v___y_3006_);
lean_dec_ref(v_post_3002_);
lean_dec_ref(v_e_3001_);
lean_dec_ref(v_pre_3000_);
v_a_3062_ = lean_ctor_get(v___x_3012_, 0);
v_isSharedCheck_3069_ = !lean_is_exclusive(v___x_3012_);
if (v_isSharedCheck_3069_ == 0)
{
v___x_3064_ = v___x_3012_;
v_isShared_3065_ = v_isSharedCheck_3069_;
goto v_resetjp_3063_;
}
else
{
lean_inc(v_a_3062_);
lean_dec(v___x_3012_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__1___boxed(lean_object* v_pre_3070_, lean_object* v_e_3071_, lean_object* v_post_3072_, lean_object* v_usedLetOnly_3073_, lean_object* v_skipConstInApp_3074_, lean_object* v_skipInstances_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_){
_start:
{
uint8_t v_usedLetOnly_boxed_3082_; uint8_t v_skipConstInApp_boxed_3083_; uint8_t v_skipInstances_boxed_3084_; lean_object* v_res_3085_; 
v_usedLetOnly_boxed_3082_ = lean_unbox(v_usedLetOnly_3073_);
v_skipConstInApp_boxed_3083_ = lean_unbox(v_skipConstInApp_3074_);
v_skipInstances_boxed_3084_ = lean_unbox(v_skipInstances_3075_);
v_res_3085_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__1(v_pre_3070_, v_e_3071_, v_post_3072_, v_usedLetOnly_boxed_3082_, v_skipConstInApp_boxed_3083_, v_skipInstances_boxed_3084_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_);
return v_res_3085_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(lean_object* v_pre_3086_, lean_object* v_post_3087_, uint8_t v_usedLetOnly_3088_, uint8_t v_skipConstInApp_3089_, uint8_t v_skipInstances_3090_, lean_object* v_e_3091_, lean_object* v_a_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_){
_start:
{
lean_object* v___x_3098_; lean_object* v___x_3099_; 
lean_inc(v_a_3092_);
v___x_3098_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3098_, 0, lean_box(0));
lean_closure_set(v___x_3098_, 1, lean_box(0));
lean_closure_set(v___x_3098_, 2, v_a_3092_);
v___x_3099_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__0(lean_box(0), v___x_3098_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_);
if (lean_obj_tag(v___x_3099_) == 0)
{
lean_object* v_a_3100_; lean_object* v___x_3102_; uint8_t v_isShared_3103_; uint8_t v_isSharedCheck_3133_; 
v_a_3100_ = lean_ctor_get(v___x_3099_, 0);
v_isSharedCheck_3133_ = !lean_is_exclusive(v___x_3099_);
if (v_isSharedCheck_3133_ == 0)
{
v___x_3102_ = v___x_3099_;
v_isShared_3103_ = v_isSharedCheck_3133_;
goto v_resetjp_3101_;
}
else
{
lean_inc(v_a_3100_);
lean_dec(v___x_3099_);
v___x_3102_ = lean_box(0);
v_isShared_3103_ = v_isSharedCheck_3133_;
goto v_resetjp_3101_;
}
v_resetjp_3101_:
{
lean_object* v___x_3104_; 
v___x_3104_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___redArg(v_a_3100_, v_e_3091_);
lean_dec(v_a_3100_);
if (lean_obj_tag(v___x_3104_) == 0)
{
lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___f_3108_; lean_object* v___x_3109_; 
lean_del_object(v___x_3102_);
v___x_3105_ = lean_box(v_usedLetOnly_3088_);
v___x_3106_ = lean_box(v_skipConstInApp_3089_);
v___x_3107_ = lean_box(v_skipInstances_3090_);
lean_inc_ref(v_e_3091_);
v___f_3108_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__1___boxed), 12, 6);
lean_closure_set(v___f_3108_, 0, v_pre_3086_);
lean_closure_set(v___f_3108_, 1, v_e_3091_);
lean_closure_set(v___f_3108_, 2, v_post_3087_);
lean_closure_set(v___f_3108_, 3, v___x_3105_);
lean_closure_set(v___f_3108_, 4, v___x_3106_);
lean_closure_set(v___f_3108_, 5, v___x_3107_);
lean_inc(v___y_3096_);
lean_inc_ref(v___y_3095_);
lean_inc(v___y_3094_);
lean_inc_ref(v___y_3093_);
lean_inc(v_a_3092_);
v___x_3109_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12___redArg(v___f_3108_, v_a_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_);
if (lean_obj_tag(v___x_3109_) == 0)
{
lean_object* v_a_3110_; lean_object* v___f_3111_; lean_object* v___x_3112_; 
v_a_3110_ = lean_ctor_get(v___x_3109_, 0);
lean_inc(v_a_3110_);
lean_dec_ref(v___x_3109_);
lean_inc(v_a_3110_);
v___f_3111_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__2___boxed), 4, 3);
lean_closure_set(v___f_3111_, 0, v_a_3092_);
lean_closure_set(v___f_3111_, 1, v_e_3091_);
lean_closure_set(v___f_3111_, 2, v_a_3110_);
v___x_3112_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__0(lean_box(0), v___f_3111_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_);
lean_dec(v___y_3096_);
lean_dec_ref(v___y_3095_);
lean_dec(v___y_3094_);
lean_dec_ref(v___y_3093_);
if (lean_obj_tag(v___x_3112_) == 0)
{
lean_object* v___x_3114_; uint8_t v_isShared_3115_; uint8_t v_isSharedCheck_3119_; 
v_isSharedCheck_3119_ = !lean_is_exclusive(v___x_3112_);
if (v_isSharedCheck_3119_ == 0)
{
lean_object* v_unused_3120_; 
v_unused_3120_ = lean_ctor_get(v___x_3112_, 0);
lean_dec(v_unused_3120_);
v___x_3114_ = v___x_3112_;
v_isShared_3115_ = v_isSharedCheck_3119_;
goto v_resetjp_3113_;
}
else
{
lean_dec(v___x_3112_);
v___x_3114_ = lean_box(0);
v_isShared_3115_ = v_isSharedCheck_3119_;
goto v_resetjp_3113_;
}
v_resetjp_3113_:
{
lean_object* v___x_3117_; 
if (v_isShared_3115_ == 0)
{
lean_ctor_set(v___x_3114_, 0, v_a_3110_);
v___x_3117_ = v___x_3114_;
goto v_reusejp_3116_;
}
else
{
lean_object* v_reuseFailAlloc_3118_; 
v_reuseFailAlloc_3118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3118_, 0, v_a_3110_);
v___x_3117_ = v_reuseFailAlloc_3118_;
goto v_reusejp_3116_;
}
v_reusejp_3116_:
{
return v___x_3117_;
}
}
}
else
{
lean_object* v_a_3121_; lean_object* v___x_3123_; uint8_t v_isShared_3124_; uint8_t v_isSharedCheck_3128_; 
lean_dec(v_a_3110_);
v_a_3121_ = lean_ctor_get(v___x_3112_, 0);
v_isSharedCheck_3128_ = !lean_is_exclusive(v___x_3112_);
if (v_isSharedCheck_3128_ == 0)
{
v___x_3123_ = v___x_3112_;
v_isShared_3124_ = v_isSharedCheck_3128_;
goto v_resetjp_3122_;
}
else
{
lean_inc(v_a_3121_);
lean_dec(v___x_3112_);
v___x_3123_ = lean_box(0);
v_isShared_3124_ = v_isSharedCheck_3128_;
goto v_resetjp_3122_;
}
v_resetjp_3122_:
{
lean_object* v___x_3126_; 
if (v_isShared_3124_ == 0)
{
v___x_3126_ = v___x_3123_;
goto v_reusejp_3125_;
}
else
{
lean_object* v_reuseFailAlloc_3127_; 
v_reuseFailAlloc_3127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3127_, 0, v_a_3121_);
v___x_3126_ = v_reuseFailAlloc_3127_;
goto v_reusejp_3125_;
}
v_reusejp_3125_:
{
return v___x_3126_;
}
}
}
}
else
{
lean_dec(v___y_3096_);
lean_dec_ref(v___y_3095_);
lean_dec(v___y_3094_);
lean_dec_ref(v___y_3093_);
lean_dec(v_a_3092_);
lean_dec_ref(v_e_3091_);
return v___x_3109_;
}
}
else
{
lean_object* v_val_3129_; lean_object* v___x_3131_; 
lean_dec(v___y_3096_);
lean_dec_ref(v___y_3095_);
lean_dec(v___y_3094_);
lean_dec_ref(v___y_3093_);
lean_dec(v_a_3092_);
lean_dec_ref(v_e_3091_);
lean_dec_ref(v_post_3087_);
lean_dec_ref(v_pre_3086_);
v_val_3129_ = lean_ctor_get(v___x_3104_, 0);
lean_inc(v_val_3129_);
lean_dec_ref(v___x_3104_);
if (v_isShared_3103_ == 0)
{
lean_ctor_set(v___x_3102_, 0, v_val_3129_);
v___x_3131_ = v___x_3102_;
goto v_reusejp_3130_;
}
else
{
lean_object* v_reuseFailAlloc_3132_; 
v_reuseFailAlloc_3132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3132_, 0, v_val_3129_);
v___x_3131_ = v_reuseFailAlloc_3132_;
goto v_reusejp_3130_;
}
v_reusejp_3130_:
{
return v___x_3131_;
}
}
}
}
else
{
lean_object* v_a_3134_; lean_object* v___x_3136_; uint8_t v_isShared_3137_; uint8_t v_isSharedCheck_3141_; 
lean_dec(v___y_3096_);
lean_dec_ref(v___y_3095_);
lean_dec(v___y_3094_);
lean_dec_ref(v___y_3093_);
lean_dec(v_a_3092_);
lean_dec_ref(v_e_3091_);
lean_dec_ref(v_post_3087_);
lean_dec_ref(v_pre_3086_);
v_a_3134_ = lean_ctor_get(v___x_3099_, 0);
v_isSharedCheck_3141_ = !lean_is_exclusive(v___x_3099_);
if (v_isSharedCheck_3141_ == 0)
{
v___x_3136_ = v___x_3099_;
v_isShared_3137_ = v_isSharedCheck_3141_;
goto v_resetjp_3135_;
}
else
{
lean_inc(v_a_3134_);
lean_dec(v___x_3099_);
v___x_3136_ = lean_box(0);
v_isShared_3137_ = v_isSharedCheck_3141_;
goto v_resetjp_3135_;
}
v_resetjp_3135_:
{
lean_object* v___x_3139_; 
if (v_isShared_3137_ == 0)
{
v___x_3139_ = v___x_3136_;
goto v_reusejp_3138_;
}
else
{
lean_object* v_reuseFailAlloc_3140_; 
v_reuseFailAlloc_3140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3140_, 0, v_a_3134_);
v___x_3139_ = v_reuseFailAlloc_3140_;
goto v_reusejp_3138_;
}
v_reusejp_3138_:
{
return v___x_3139_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8___lam__0___boxed(lean_object* v_fvars_3142_, lean_object* v_pre_3143_, lean_object* v_post_3144_, lean_object* v_usedLetOnly_3145_, lean_object* v_skipConstInApp_3146_, lean_object* v_skipInstances_3147_, lean_object* v_body_3148_, lean_object* v_x_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_){
_start:
{
uint8_t v_usedLetOnly_boxed_3156_; uint8_t v_skipConstInApp_boxed_3157_; uint8_t v_skipInstances_boxed_3158_; lean_object* v_res_3159_; 
v_usedLetOnly_boxed_3156_ = lean_unbox(v_usedLetOnly_3145_);
v_skipConstInApp_boxed_3157_ = lean_unbox(v_skipConstInApp_3146_);
v_skipInstances_boxed_3158_ = lean_unbox(v_skipInstances_3147_);
v_res_3159_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8___lam__0(v_fvars_3142_, v_pre_3143_, v_post_3144_, v_usedLetOnly_boxed_3156_, v_skipConstInApp_boxed_3157_, v_skipInstances_boxed_3158_, v_body_3148_, v_x_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_);
return v_res_3159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8(lean_object* v_pre_3160_, lean_object* v_post_3161_, uint8_t v_usedLetOnly_3162_, uint8_t v_skipConstInApp_3163_, uint8_t v_skipInstances_3164_, lean_object* v_fvars_3165_, lean_object* v_e_3166_, lean_object* v_a_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_){
_start:
{
if (lean_obj_tag(v_e_3166_) == 7)
{
lean_object* v_binderName_3173_; lean_object* v_binderType_3174_; lean_object* v_body_3175_; uint8_t v_binderInfo_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; 
v_binderName_3173_ = lean_ctor_get(v_e_3166_, 0);
lean_inc(v_binderName_3173_);
v_binderType_3174_ = lean_ctor_get(v_e_3166_, 1);
lean_inc_ref(v_binderType_3174_);
v_body_3175_ = lean_ctor_get(v_e_3166_, 2);
lean_inc_ref(v_body_3175_);
v_binderInfo_3176_ = lean_ctor_get_uint8(v_e_3166_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_3166_);
v___x_3177_ = lean_expr_instantiate_rev(v_binderType_3174_, v_fvars_3165_);
lean_dec_ref(v_binderType_3174_);
lean_inc(v___y_3171_);
lean_inc_ref(v___y_3170_);
lean_inc(v___y_3169_);
lean_inc_ref(v___y_3168_);
lean_inc(v_a_3167_);
lean_inc_ref(v_post_3161_);
lean_inc_ref(v_pre_3160_);
v___x_3178_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_3160_, v_post_3161_, v_usedLetOnly_3162_, v_skipConstInApp_3163_, v_skipInstances_3164_, v___x_3177_, v_a_3167_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_);
if (lean_obj_tag(v___x_3178_) == 0)
{
lean_object* v_a_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___f_3183_; uint8_t v___x_3184_; lean_object* v___x_3185_; 
v_a_3179_ = lean_ctor_get(v___x_3178_, 0);
lean_inc(v_a_3179_);
lean_dec_ref(v___x_3178_);
v___x_3180_ = lean_box(v_usedLetOnly_3162_);
v___x_3181_ = lean_box(v_skipConstInApp_3163_);
v___x_3182_ = lean_box(v_skipInstances_3164_);
v___f_3183_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8___lam__0___boxed), 14, 7);
lean_closure_set(v___f_3183_, 0, v_fvars_3165_);
lean_closure_set(v___f_3183_, 1, v_pre_3160_);
lean_closure_set(v___f_3183_, 2, v_post_3161_);
lean_closure_set(v___f_3183_, 3, v___x_3180_);
lean_closure_set(v___f_3183_, 4, v___x_3181_);
lean_closure_set(v___f_3183_, 5, v___x_3182_);
lean_closure_set(v___f_3183_, 6, v_body_3175_);
v___x_3184_ = 0;
v___x_3185_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg(v_binderName_3173_, v_binderInfo_3176_, v_a_3179_, v___f_3183_, v___x_3184_, v_a_3167_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_);
return v___x_3185_;
}
else
{
lean_dec_ref(v_body_3175_);
lean_dec(v_binderName_3173_);
lean_dec(v___y_3171_);
lean_dec_ref(v___y_3170_);
lean_dec(v___y_3169_);
lean_dec_ref(v___y_3168_);
lean_dec(v_a_3167_);
lean_dec_ref(v_fvars_3165_);
lean_dec_ref(v_post_3161_);
lean_dec_ref(v_pre_3160_);
return v___x_3178_;
}
}
else
{
lean_object* v___x_3186_; lean_object* v___x_3187_; 
v___x_3186_ = lean_expr_instantiate_rev(v_e_3166_, v_fvars_3165_);
lean_dec_ref(v_e_3166_);
lean_inc(v___y_3171_);
lean_inc_ref(v___y_3170_);
lean_inc(v___y_3169_);
lean_inc_ref(v___y_3168_);
lean_inc(v_a_3167_);
lean_inc_ref(v_post_3161_);
lean_inc_ref(v_pre_3160_);
v___x_3187_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_3160_, v_post_3161_, v_usedLetOnly_3162_, v_skipConstInApp_3163_, v_skipInstances_3164_, v___x_3186_, v_a_3167_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_);
if (lean_obj_tag(v___x_3187_) == 0)
{
lean_object* v_a_3188_; uint8_t v___x_3189_; uint8_t v___x_3190_; uint8_t v___x_3191_; lean_object* v___x_3192_; 
v_a_3188_ = lean_ctor_get(v___x_3187_, 0);
lean_inc(v_a_3188_);
lean_dec_ref(v___x_3187_);
v___x_3189_ = 0;
v___x_3190_ = 1;
v___x_3191_ = 1;
v___x_3192_ = l_Lean_Meta_mkForallFVars(v_fvars_3165_, v_a_3188_, v___x_3189_, v_usedLetOnly_3162_, v___x_3190_, v___x_3191_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_);
lean_dec_ref(v_fvars_3165_);
if (lean_obj_tag(v___x_3192_) == 0)
{
lean_object* v_a_3193_; lean_object* v___x_3194_; 
v_a_3193_ = lean_ctor_get(v___x_3192_, 0);
lean_inc(v_a_3193_);
lean_dec_ref(v___x_3192_);
v___x_3194_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_3160_, v_post_3161_, v_usedLetOnly_3162_, v_skipConstInApp_3163_, v_skipInstances_3164_, v_a_3193_, v_a_3167_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_);
return v___x_3194_;
}
else
{
lean_dec(v___y_3171_);
lean_dec_ref(v___y_3170_);
lean_dec(v___y_3169_);
lean_dec_ref(v___y_3168_);
lean_dec(v_a_3167_);
lean_dec_ref(v_post_3161_);
lean_dec_ref(v_pre_3160_);
return v___x_3192_;
}
}
else
{
lean_dec(v___y_3171_);
lean_dec_ref(v___y_3170_);
lean_dec(v___y_3169_);
lean_dec_ref(v___y_3168_);
lean_dec(v_a_3167_);
lean_dec_ref(v_fvars_3165_);
lean_dec_ref(v_post_3161_);
lean_dec_ref(v_pre_3160_);
return v___x_3187_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8___lam__0(lean_object* v_fvars_3195_, lean_object* v_pre_3196_, lean_object* v_post_3197_, uint8_t v_usedLetOnly_3198_, uint8_t v_skipConstInApp_3199_, uint8_t v_skipInstances_3200_, lean_object* v_body_3201_, lean_object* v_x_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_){
_start:
{
lean_object* v___x_3209_; lean_object* v___x_3210_; 
v___x_3209_ = lean_array_push(v_fvars_3195_, v_x_3202_);
v___x_3210_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8(v_pre_3196_, v_post_3197_, v_usedLetOnly_3198_, v_skipConstInApp_3199_, v_skipInstances_3200_, v___x_3209_, v_body_3201_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_);
return v___x_3210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5___boxed(lean_object* v_pre_3211_, lean_object* v_post_3212_, lean_object* v_usedLetOnly_3213_, lean_object* v_skipConstInApp_3214_, lean_object* v_skipInstances_3215_, lean_object* v_e_3216_, lean_object* v_a_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_){
_start:
{
uint8_t v_usedLetOnly_boxed_3223_; uint8_t v_skipConstInApp_boxed_3224_; uint8_t v_skipInstances_boxed_3225_; lean_object* v_res_3226_; 
v_usedLetOnly_boxed_3223_ = lean_unbox(v_usedLetOnly_3213_);
v_skipConstInApp_boxed_3224_ = lean_unbox(v_skipConstInApp_3214_);
v_skipInstances_boxed_3225_ = lean_unbox(v_skipInstances_3215_);
v_res_3226_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_3211_, v_post_3212_, v_usedLetOnly_boxed_3223_, v_skipConstInApp_boxed_3224_, v_skipInstances_boxed_3225_, v_e_3216_, v_a_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_);
return v_res_3226_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__4___boxed(lean_object* v_pre_3227_, lean_object* v_post_3228_, lean_object* v_usedLetOnly_3229_, lean_object* v_skipConstInApp_3230_, lean_object* v_skipInstances_3231_, lean_object* v_sz_3232_, lean_object* v_i_3233_, lean_object* v_bs_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_){
_start:
{
uint8_t v_usedLetOnly_boxed_3241_; uint8_t v_skipConstInApp_boxed_3242_; uint8_t v_skipInstances_boxed_3243_; size_t v_sz_boxed_3244_; size_t v_i_boxed_3245_; lean_object* v_res_3246_; 
v_usedLetOnly_boxed_3241_ = lean_unbox(v_usedLetOnly_3229_);
v_skipConstInApp_boxed_3242_ = lean_unbox(v_skipConstInApp_3230_);
v_skipInstances_boxed_3243_ = lean_unbox(v_skipInstances_3231_);
v_sz_boxed_3244_ = lean_unbox_usize(v_sz_3232_);
lean_dec(v_sz_3232_);
v_i_boxed_3245_ = lean_unbox_usize(v_i_3233_);
lean_dec(v_i_3233_);
v_res_3246_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__4(v_pre_3227_, v_post_3228_, v_usedLetOnly_boxed_3241_, v_skipConstInApp_boxed_3242_, v_skipInstances_boxed_3243_, v_sz_boxed_3244_, v_i_boxed_3245_, v_bs_3234_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_, v___y_3239_);
return v_res_3246_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___boxed(lean_object* v_pre_3247_, lean_object* v_post_3248_, lean_object* v_usedLetOnly_3249_, lean_object* v_skipConstInApp_3250_, lean_object* v_skipInstances_3251_, lean_object* v_e_3252_, lean_object* v_a_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_){
_start:
{
uint8_t v_usedLetOnly_boxed_3259_; uint8_t v_skipConstInApp_boxed_3260_; uint8_t v_skipInstances_boxed_3261_; lean_object* v_res_3262_; 
v_usedLetOnly_boxed_3259_ = lean_unbox(v_usedLetOnly_3249_);
v_skipConstInApp_boxed_3260_ = lean_unbox(v_skipConstInApp_3250_);
v_skipInstances_boxed_3261_ = lean_unbox(v_skipInstances_3251_);
v_res_3262_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_3247_, v_post_3248_, v_usedLetOnly_boxed_3259_, v_skipConstInApp_boxed_3260_, v_skipInstances_boxed_3261_, v_e_3252_, v_a_3253_, v___y_3254_, v___y_3255_, v___y_3256_, v___y_3257_);
return v_res_3262_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8___boxed(lean_object* v_pre_3263_, lean_object* v_post_3264_, lean_object* v_usedLetOnly_3265_, lean_object* v_skipConstInApp_3266_, lean_object* v_skipInstances_3267_, lean_object* v_fvars_3268_, lean_object* v_e_3269_, lean_object* v_a_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_){
_start:
{
uint8_t v_usedLetOnly_boxed_3276_; uint8_t v_skipConstInApp_boxed_3277_; uint8_t v_skipInstances_boxed_3278_; lean_object* v_res_3279_; 
v_usedLetOnly_boxed_3276_ = lean_unbox(v_usedLetOnly_3265_);
v_skipConstInApp_boxed_3277_ = lean_unbox(v_skipConstInApp_3266_);
v_skipInstances_boxed_3278_ = lean_unbox(v_skipInstances_3267_);
v_res_3279_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8(v_pre_3263_, v_post_3264_, v_usedLetOnly_boxed_3276_, v_skipConstInApp_boxed_3277_, v_skipInstances_boxed_3278_, v_fvars_3268_, v_e_3269_, v_a_3270_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_);
return v_res_3279_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9___boxed(lean_object* v_pre_3280_, lean_object* v_post_3281_, lean_object* v_usedLetOnly_3282_, lean_object* v_skipConstInApp_3283_, lean_object* v_skipInstances_3284_, lean_object* v_fvars_3285_, lean_object* v_e_3286_, lean_object* v_a_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_){
_start:
{
uint8_t v_usedLetOnly_boxed_3293_; uint8_t v_skipConstInApp_boxed_3294_; uint8_t v_skipInstances_boxed_3295_; lean_object* v_res_3296_; 
v_usedLetOnly_boxed_3293_ = lean_unbox(v_usedLetOnly_3282_);
v_skipConstInApp_boxed_3294_ = lean_unbox(v_skipConstInApp_3283_);
v_skipInstances_boxed_3295_ = lean_unbox(v_skipInstances_3284_);
v_res_3296_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9(v_pre_3280_, v_post_3281_, v_usedLetOnly_boxed_3293_, v_skipConstInApp_boxed_3294_, v_skipInstances_boxed_3295_, v_fvars_3285_, v_e_3286_, v_a_3287_, v___y_3288_, v___y_3289_, v___y_3290_, v___y_3291_);
return v_res_3296_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10___boxed(lean_object* v_pre_3297_, lean_object* v_post_3298_, lean_object* v_usedLetOnly_3299_, lean_object* v_skipConstInApp_3300_, lean_object* v_skipInstances_3301_, lean_object* v_fvars_3302_, lean_object* v_e_3303_, lean_object* v_a_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_){
_start:
{
uint8_t v_usedLetOnly_boxed_3310_; uint8_t v_skipConstInApp_boxed_3311_; uint8_t v_skipInstances_boxed_3312_; lean_object* v_res_3313_; 
v_usedLetOnly_boxed_3310_ = lean_unbox(v_usedLetOnly_3299_);
v_skipConstInApp_boxed_3311_ = lean_unbox(v_skipConstInApp_3300_);
v_skipInstances_boxed_3312_ = lean_unbox(v_skipInstances_3301_);
v_res_3313_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10(v_pre_3297_, v_post_3298_, v_usedLetOnly_boxed_3310_, v_skipConstInApp_boxed_3311_, v_skipInstances_boxed_3312_, v_fvars_3302_, v_e_3303_, v_a_3304_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_);
return v_res_3313_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___boxed(lean_object* v_upperBound_3314_, lean_object* v___x_3315_, lean_object* v_pre_3316_, lean_object* v_post_3317_, lean_object* v_usedLetOnly_3318_, lean_object* v_skipConstInApp_3319_, lean_object* v_skipInstances_3320_, lean_object* v_a_3321_, lean_object* v_b_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_){
_start:
{
uint8_t v_usedLetOnly_boxed_3329_; uint8_t v_skipConstInApp_boxed_3330_; uint8_t v_skipInstances_boxed_3331_; lean_object* v_res_3332_; 
v_usedLetOnly_boxed_3329_ = lean_unbox(v_usedLetOnly_3318_);
v_skipConstInApp_boxed_3330_ = lean_unbox(v_skipConstInApp_3319_);
v_skipInstances_boxed_3331_ = lean_unbox(v_skipInstances_3320_);
v_res_3332_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg(v_upperBound_3314_, v___x_3315_, v_pre_3316_, v_post_3317_, v_usedLetOnly_boxed_3329_, v_skipConstInApp_boxed_3330_, v_skipInstances_boxed_3331_, v_a_3321_, v_b_3322_, v___y_3323_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_);
lean_dec_ref(v___x_3315_);
lean_dec(v_upperBound_3314_);
return v_res_3332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__11___boxed(lean_object* v_skipInstances_3333_, lean_object* v_pre_3334_, lean_object* v_post_3335_, lean_object* v_usedLetOnly_3336_, lean_object* v_skipConstInApp_3337_, lean_object* v_x_3338_, lean_object* v_x_3339_, lean_object* v_x_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_){
_start:
{
uint8_t v_skipInstances_boxed_3347_; uint8_t v_usedLetOnly_boxed_3348_; uint8_t v_skipConstInApp_boxed_3349_; lean_object* v_res_3350_; 
v_skipInstances_boxed_3347_ = lean_unbox(v_skipInstances_3333_);
v_usedLetOnly_boxed_3348_ = lean_unbox(v_usedLetOnly_3336_);
v_skipConstInApp_boxed_3349_ = lean_unbox(v_skipConstInApp_3337_);
v_res_3350_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__11(v_skipInstances_boxed_3347_, v_pre_3334_, v_post_3335_, v_usedLetOnly_boxed_3348_, v_skipConstInApp_boxed_3349_, v_x_3338_, v_x_3339_, v_x_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_);
return v_res_3350_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__0(void){
_start:
{
lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; 
v___x_3351_ = lean_box(0);
v___x_3352_ = lean_unsigned_to_nat(16u);
v___x_3353_ = lean_mk_array(v___x_3352_, v___x_3351_);
return v___x_3353_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__1(void){
_start:
{
lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; 
v___x_3354_ = lean_obj_once(&l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__0, &l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__0_once, _init_l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__0);
v___x_3355_ = lean_unsigned_to_nat(0u);
v___x_3356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3356_, 0, v___x_3355_);
lean_ctor_set(v___x_3356_, 1, v___x_3354_);
return v___x_3356_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__2(void){
_start:
{
lean_object* v___x_3357_; lean_object* v___x_3358_; 
v___x_3357_ = lean_obj_once(&l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__1, &l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__1_once, _init_l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__1);
v___x_3358_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_3358_, 0, lean_box(0));
lean_closure_set(v___x_3358_, 1, lean_box(0));
lean_closure_set(v___x_3358_, 2, v___x_3357_);
return v___x_3358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3(lean_object* v_input_3359_, lean_object* v_pre_3360_, lean_object* v_post_3361_, uint8_t v_usedLetOnly_3362_, uint8_t v_skipConstInApp_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_){
_start:
{
lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v_a_3371_; uint8_t v___x_3372_; lean_object* v___x_3373_; 
v___x_3369_ = lean_obj_once(&l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__2, &l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__2_once, _init_l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__2);
v___x_3370_ = l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___lam__0(lean_box(0), v___x_3369_, v___y_3364_, v___y_3365_, v___y_3366_, v___y_3367_);
v_a_3371_ = lean_ctor_get(v___x_3370_, 0);
lean_inc(v_a_3371_);
lean_dec_ref(v___x_3370_);
v___x_3372_ = 0;
lean_inc(v___y_3367_);
lean_inc_ref(v___y_3366_);
lean_inc(v___y_3365_);
lean_inc_ref(v___y_3364_);
lean_inc(v_a_3371_);
v___x_3373_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_3360_, v_post_3361_, v_usedLetOnly_3362_, v_skipConstInApp_3363_, v___x_3372_, v_input_3359_, v_a_3371_, v___y_3364_, v___y_3365_, v___y_3366_, v___y_3367_);
if (lean_obj_tag(v___x_3373_) == 0)
{
lean_object* v_a_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3378_; uint8_t v_isShared_3379_; uint8_t v_isSharedCheck_3383_; 
v_a_3374_ = lean_ctor_get(v___x_3373_, 0);
lean_inc(v_a_3374_);
lean_dec_ref(v___x_3373_);
v___x_3375_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3375_, 0, lean_box(0));
lean_closure_set(v___x_3375_, 1, lean_box(0));
lean_closure_set(v___x_3375_, 2, v_a_3371_);
v___x_3376_ = l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___lam__0(lean_box(0), v___x_3375_, v___y_3364_, v___y_3365_, v___y_3366_, v___y_3367_);
lean_dec(v___y_3367_);
lean_dec_ref(v___y_3366_);
lean_dec(v___y_3365_);
lean_dec_ref(v___y_3364_);
v_isSharedCheck_3383_ = !lean_is_exclusive(v___x_3376_);
if (v_isSharedCheck_3383_ == 0)
{
lean_object* v_unused_3384_; 
v_unused_3384_ = lean_ctor_get(v___x_3376_, 0);
lean_dec(v_unused_3384_);
v___x_3378_ = v___x_3376_;
v_isShared_3379_ = v_isSharedCheck_3383_;
goto v_resetjp_3377_;
}
else
{
lean_dec(v___x_3376_);
v___x_3378_ = lean_box(0);
v_isShared_3379_ = v_isSharedCheck_3383_;
goto v_resetjp_3377_;
}
v_resetjp_3377_:
{
lean_object* v___x_3381_; 
if (v_isShared_3379_ == 0)
{
lean_ctor_set(v___x_3378_, 0, v_a_3374_);
v___x_3381_ = v___x_3378_;
goto v_reusejp_3380_;
}
else
{
lean_object* v_reuseFailAlloc_3382_; 
v_reuseFailAlloc_3382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3382_, 0, v_a_3374_);
v___x_3381_ = v_reuseFailAlloc_3382_;
goto v_reusejp_3380_;
}
v_reusejp_3380_:
{
return v___x_3381_;
}
}
}
else
{
lean_dec(v_a_3371_);
lean_dec(v___y_3367_);
lean_dec_ref(v___y_3366_);
lean_dec(v___y_3365_);
lean_dec_ref(v___y_3364_);
return v___x_3373_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___boxed(lean_object* v_input_3385_, lean_object* v_pre_3386_, lean_object* v_post_3387_, lean_object* v_usedLetOnly_3388_, lean_object* v_skipConstInApp_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_){
_start:
{
uint8_t v_usedLetOnly_boxed_3395_; uint8_t v_skipConstInApp_boxed_3396_; lean_object* v_res_3397_; 
v_usedLetOnly_boxed_3395_ = lean_unbox(v_usedLetOnly_3388_);
v_skipConstInApp_boxed_3396_ = lean_unbox(v_skipConstInApp_3389_);
v_res_3397_ = l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3(v_input_3385_, v_pre_3386_, v_post_3387_, v_usedLetOnly_boxed_3395_, v_skipConstInApp_boxed_3396_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_);
return v_res_3397_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet(lean_object* v_e_3400_, lean_object* v_a_3401_, lean_object* v_a_3402_, lean_object* v_a_3403_, lean_object* v_a_3404_){
_start:
{
lean_object* v___f_3406_; lean_object* v___f_3407_; uint8_t v___x_3408_; lean_object* v___x_3409_; 
v___f_3406_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___closed__0));
v___f_3407_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___closed__1));
v___x_3408_ = 0;
v___x_3409_ = l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3(v_e_3400_, v___f_3407_, v___f_3406_, v___x_3408_, v___x_3408_, v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_);
return v___x_3409_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___boxed(lean_object* v_e_3410_, lean_object* v_a_3411_, lean_object* v_a_3412_, lean_object* v_a_3413_, lean_object* v_a_3414_, lean_object* v_a_3415_){
_start:
{
lean_object* v_res_3416_; 
v_res_3416_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet(v_e_3410_, v_a_3411_, v_a_3412_, v_a_3413_, v_a_3414_);
return v_res_3416_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6(lean_object* v_upperBound_3417_, lean_object* v___x_3418_, lean_object* v_pre_3419_, lean_object* v_post_3420_, uint8_t v_usedLetOnly_3421_, uint8_t v_skipConstInApp_3422_, uint8_t v_skipInstances_3423_, lean_object* v___x_3424_, lean_object* v_inst_3425_, lean_object* v_R_3426_, lean_object* v_a_3427_, lean_object* v_b_3428_, lean_object* v_c_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_){
_start:
{
lean_object* v___x_3436_; 
v___x_3436_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg(v_upperBound_3417_, v___x_3418_, v_pre_3419_, v_post_3420_, v_usedLetOnly_3421_, v_skipConstInApp_3422_, v_skipInstances_3423_, v_a_3427_, v_b_3428_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_);
return v___x_3436_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___boxed(lean_object** _args){
lean_object* v_upperBound_3437_ = _args[0];
lean_object* v___x_3438_ = _args[1];
lean_object* v_pre_3439_ = _args[2];
lean_object* v_post_3440_ = _args[3];
lean_object* v_usedLetOnly_3441_ = _args[4];
lean_object* v_skipConstInApp_3442_ = _args[5];
lean_object* v_skipInstances_3443_ = _args[6];
lean_object* v___x_3444_ = _args[7];
lean_object* v_inst_3445_ = _args[8];
lean_object* v_R_3446_ = _args[9];
lean_object* v_a_3447_ = _args[10];
lean_object* v_b_3448_ = _args[11];
lean_object* v_c_3449_ = _args[12];
lean_object* v___y_3450_ = _args[13];
lean_object* v___y_3451_ = _args[14];
lean_object* v___y_3452_ = _args[15];
lean_object* v___y_3453_ = _args[16];
lean_object* v___y_3454_ = _args[17];
lean_object* v___y_3455_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_3456_; uint8_t v_skipConstInApp_boxed_3457_; uint8_t v_skipInstances_boxed_3458_; lean_object* v_res_3459_; 
v_usedLetOnly_boxed_3456_ = lean_unbox(v_usedLetOnly_3441_);
v_skipConstInApp_boxed_3457_ = lean_unbox(v_skipConstInApp_3442_);
v_skipInstances_boxed_3458_ = lean_unbox(v_skipInstances_3443_);
v_res_3459_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6(v_upperBound_3437_, v___x_3438_, v_pre_3439_, v_post_3440_, v_usedLetOnly_boxed_3456_, v_skipConstInApp_boxed_3457_, v_skipInstances_boxed_3458_, v___x_3444_, v_inst_3445_, v_R_3446_, v_a_3447_, v_b_3448_, v_c_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_);
lean_dec(v___x_3444_);
lean_dec_ref(v___x_3438_);
lean_dec(v_upperBound_3437_);
return v_res_3459_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7(lean_object* v_00_u03b2_3460_, lean_object* v_m_3461_, lean_object* v_a_3462_){
_start:
{
lean_object* v___x_3463_; 
v___x_3463_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___redArg(v_m_3461_, v_a_3462_);
return v___x_3463_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___boxed(lean_object* v_00_u03b2_3464_, lean_object* v_m_3465_, lean_object* v_a_3466_){
_start:
{
lean_object* v_res_3467_; 
v_res_3467_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7(v_00_u03b2_3464_, v_m_3465_, v_a_3466_);
lean_dec_ref(v_a_3466_);
lean_dec_ref(v_m_3465_);
return v_res_3467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10(lean_object* v_00_u03b1_3468_, lean_object* v_name_3469_, uint8_t v_bi_3470_, lean_object* v_type_3471_, lean_object* v_k_3472_, uint8_t v_kind_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_){
_start:
{
lean_object* v___x_3480_; 
v___x_3480_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg(v_name_3469_, v_bi_3470_, v_type_3471_, v_k_3472_, v_kind_3473_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_);
return v___x_3480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___boxed(lean_object* v_00_u03b1_3481_, lean_object* v_name_3482_, lean_object* v_bi_3483_, lean_object* v_type_3484_, lean_object* v_k_3485_, lean_object* v_kind_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_){
_start:
{
uint8_t v_bi_boxed_3493_; uint8_t v_kind_boxed_3494_; lean_object* v_res_3495_; 
v_bi_boxed_3493_ = lean_unbox(v_bi_3483_);
v_kind_boxed_3494_ = lean_unbox(v_kind_3486_);
v_res_3495_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10(v_00_u03b1_3481_, v_name_3482_, v_bi_boxed_3493_, v_type_3484_, v_k_3485_, v_kind_boxed_3494_, v___y_3487_, v___y_3488_, v___y_3489_, v___y_3490_, v___y_3491_);
return v_res_3495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13(lean_object* v_00_u03b1_3496_, lean_object* v_name_3497_, lean_object* v_type_3498_, lean_object* v_val_3499_, lean_object* v_k_3500_, uint8_t v_nondep_3501_, uint8_t v_kind_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_){
_start:
{
lean_object* v___x_3509_; 
v___x_3509_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13___redArg(v_name_3497_, v_type_3498_, v_val_3499_, v_k_3500_, v_nondep_3501_, v_kind_3502_, v___y_3503_, v___y_3504_, v___y_3505_, v___y_3506_, v___y_3507_);
return v___x_3509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13___boxed(lean_object* v_00_u03b1_3510_, lean_object* v_name_3511_, lean_object* v_type_3512_, lean_object* v_val_3513_, lean_object* v_k_3514_, lean_object* v_nondep_3515_, lean_object* v_kind_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_){
_start:
{
uint8_t v_nondep_boxed_3523_; uint8_t v_kind_boxed_3524_; lean_object* v_res_3525_; 
v_nondep_boxed_3523_ = lean_unbox(v_nondep_3515_);
v_kind_boxed_3524_ = lean_unbox(v_kind_3516_);
v_res_3525_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13(v_00_u03b1_3510_, v_name_3511_, v_type_3512_, v_val_3513_, v_k_3514_, v_nondep_boxed_3523_, v_kind_boxed_3524_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_);
return v_res_3525_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16(lean_object* v_00_u03b1_3526_, lean_object* v_ref_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_){
_start:
{
lean_object* v___x_3533_; 
v___x_3533_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg(v_ref_3527_);
return v___x_3533_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___boxed(lean_object* v_00_u03b1_3534_, lean_object* v_ref_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_){
_start:
{
lean_object* v_res_3541_; 
v_res_3541_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16(v_00_u03b1_3534_, v_ref_3535_, v___y_3536_, v___y_3537_, v___y_3538_, v___y_3539_);
lean_dec(v___y_3539_);
lean_dec_ref(v___y_3538_);
lean_dec(v___y_3537_);
lean_dec_ref(v___y_3536_);
return v_res_3541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12(lean_object* v_00_u03b1_3542_, lean_object* v_x_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_){
_start:
{
lean_object* v___x_3550_; 
v___x_3550_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12___redArg(v_x_3543_, v___y_3544_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_);
return v___x_3550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12___boxed(lean_object* v_00_u03b1_3551_, lean_object* v_x_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_){
_start:
{
lean_object* v_res_3559_; 
v_res_3559_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12(v_00_u03b1_3551_, v_x_3552_, v___y_3553_, v___y_3554_, v___y_3555_, v___y_3556_, v___y_3557_);
return v_res_3559_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13(lean_object* v_00_u03b2_3560_, lean_object* v_m_3561_, lean_object* v_a_3562_, lean_object* v_b_3563_){
_start:
{
lean_object* v___x_3564_; 
v___x_3564_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13___redArg(v_m_3561_, v_a_3562_, v_b_3563_);
return v___x_3564_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7_spec__8(lean_object* v_00_u03b2_3565_, lean_object* v_a_3566_, lean_object* v_x_3567_){
_start:
{
lean_object* v___x_3568_; 
v___x_3568_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7_spec__8___redArg(v_a_3566_, v_x_3567_);
return v___x_3568_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7_spec__8___boxed(lean_object* v_00_u03b2_3569_, lean_object* v_a_3570_, lean_object* v_x_3571_){
_start:
{
lean_object* v_res_3572_; 
v_res_3572_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7_spec__8(v_00_u03b2_3569_, v_a_3570_, v_x_3571_);
lean_dec(v_x_3571_);
lean_dec_ref(v_a_3570_);
return v_res_3572_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18(lean_object* v_00_u03b2_3573_, lean_object* v_a_3574_, lean_object* v_x_3575_){
_start:
{
uint8_t v___x_3576_; 
v___x_3576_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18___redArg(v_a_3574_, v_x_3575_);
return v___x_3576_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18___boxed(lean_object* v_00_u03b2_3577_, lean_object* v_a_3578_, lean_object* v_x_3579_){
_start:
{
uint8_t v_res_3580_; lean_object* v_r_3581_; 
v_res_3580_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18(v_00_u03b2_3577_, v_a_3578_, v_x_3579_);
lean_dec(v_x_3579_);
lean_dec_ref(v_a_3578_);
v_r_3581_ = lean_box(v_res_3580_);
return v_r_3581_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19(lean_object* v_00_u03b2_3582_, lean_object* v_data_3583_){
_start:
{
lean_object* v___x_3584_; 
v___x_3584_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19___redArg(v_data_3583_);
return v___x_3584_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__20(lean_object* v_00_u03b2_3585_, lean_object* v_a_3586_, lean_object* v_b_3587_, lean_object* v_x_3588_){
_start:
{
lean_object* v___x_3589_; 
v___x_3589_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__20___redArg(v_a_3586_, v_b_3587_, v_x_3588_);
return v___x_3589_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19_spec__20(lean_object* v_00_u03b2_3590_, lean_object* v_i_3591_, lean_object* v_source_3592_, lean_object* v_target_3593_){
_start:
{
lean_object* v___x_3594_; 
v___x_3594_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19_spec__20___redArg(v_i_3591_, v_source_3592_, v_target_3593_);
return v___x_3594_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19_spec__20_spec__21(lean_object* v_00_u03b2_3595_, lean_object* v_x_3596_, lean_object* v_x_3597_){
_start:
{
lean_object* v___x_3598_; 
v___x_3598_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19_spec__20_spec__21___redArg(v_x_3596_, v_x_3597_);
return v___x_3598_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_WF_preprocess_spec__1(lean_object* v_opts_3599_, lean_object* v_opt_3600_){
_start:
{
lean_object* v_name_3601_; lean_object* v_defValue_3602_; lean_object* v_map_3603_; lean_object* v___x_3604_; 
v_name_3601_ = lean_ctor_get(v_opt_3600_, 0);
v_defValue_3602_ = lean_ctor_get(v_opt_3600_, 1);
v_map_3603_ = lean_ctor_get(v_opts_3599_, 0);
v___x_3604_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3603_, v_name_3601_);
if (lean_obj_tag(v___x_3604_) == 0)
{
uint8_t v___x_3605_; 
v___x_3605_ = lean_unbox(v_defValue_3602_);
return v___x_3605_;
}
else
{
lean_object* v_val_3606_; 
v_val_3606_ = lean_ctor_get(v___x_3604_, 0);
lean_inc(v_val_3606_);
lean_dec_ref(v___x_3604_);
if (lean_obj_tag(v_val_3606_) == 1)
{
uint8_t v_v_3607_; 
v_v_3607_ = lean_ctor_get_uint8(v_val_3606_, 0);
lean_dec_ref(v_val_3606_);
return v_v_3607_;
}
else
{
uint8_t v___x_3608_; 
lean_dec(v_val_3606_);
v___x_3608_ = lean_unbox(v_defValue_3602_);
return v___x_3608_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_WF_preprocess_spec__1___boxed(lean_object* v_opts_3609_, lean_object* v_opt_3610_){
_start:
{
uint8_t v_res_3611_; lean_object* v_r_3612_; 
v_res_3611_ = l_Lean_Option_get___at___00Lean_Elab_WF_preprocess_spec__1(v_opts_3609_, v_opt_3610_);
lean_dec_ref(v_opt_3610_);
lean_dec_ref(v_opts_3609_);
v_r_3612_ = lean_box(v_res_3611_);
return v_r_3612_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___closed__0(void){
_start:
{
lean_object* v___x_3613_; 
v___x_3613_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3613_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___closed__1(void){
_start:
{
lean_object* v___x_3614_; lean_object* v___x_3615_; 
v___x_3614_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___closed__0);
v___x_3615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3615_, 0, v___x_3614_);
return v___x_3615_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3(lean_object* v_00_u03b2_3616_){
_start:
{
lean_object* v___x_3617_; 
v___x_3617_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___closed__1);
return v___x_3617_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_WF_preprocess_spec__5___redArg(lean_object* v_cls_3621_, lean_object* v___y_3622_){
_start:
{
lean_object* v_options_3624_; uint8_t v_hasTrace_3625_; 
v_options_3624_ = lean_ctor_get(v___y_3622_, 2);
v_hasTrace_3625_ = lean_ctor_get_uint8(v_options_3624_, sizeof(void*)*1);
if (v_hasTrace_3625_ == 0)
{
lean_object* v___x_3626_; lean_object* v___x_3627_; 
lean_dec(v_cls_3621_);
v___x_3626_ = lean_box(v_hasTrace_3625_);
v___x_3627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3627_, 0, v___x_3626_);
return v___x_3627_;
}
else
{
lean_object* v_inheritedTraceOptions_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; uint8_t v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; 
v_inheritedTraceOptions_3628_ = lean_ctor_get(v___y_3622_, 13);
v___x_3629_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Elab_WF_preprocess_spec__5___redArg___closed__1));
v___x_3630_ = l_Lean_Name_append(v___x_3629_, v_cls_3621_);
v___x_3631_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3628_, v_options_3624_, v___x_3630_);
lean_dec(v___x_3630_);
v___x_3632_ = lean_box(v___x_3631_);
v___x_3633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3633_, 0, v___x_3632_);
return v___x_3633_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_WF_preprocess_spec__5___redArg___boxed(lean_object* v_cls_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_){
_start:
{
lean_object* v_res_3637_; 
v_res_3637_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_WF_preprocess_spec__5___redArg(v_cls_3634_, v___y_3635_);
lean_dec_ref(v___y_3635_);
return v_res_3637_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_WF_preprocess_spec__5(lean_object* v_cls_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_){
_start:
{
lean_object* v___x_3644_; 
v___x_3644_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_WF_preprocess_spec__5___redArg(v_cls_3638_, v___y_3641_);
return v___x_3644_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_WF_preprocess_spec__5___boxed(lean_object* v_cls_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_){
_start:
{
lean_object* v_res_3651_; 
v_res_3651_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_WF_preprocess_spec__5(v_cls_3645_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_);
lean_dec(v___y_3649_);
lean_dec_ref(v___y_3648_);
lean_dec(v___y_3647_);
lean_dec_ref(v___y_3646_);
return v_res_3651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__7___redArg(lean_object* v_e_3652_, lean_object* v_k_3653_, uint8_t v_cleanupAnnotations_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_){
_start:
{
lean_object* v___f_3660_; uint8_t v___x_3661_; uint8_t v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; 
v___f_3660_ = lean_alloc_closure((void*)(l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3660_, 0, v_k_3653_);
v___x_3661_ = 1;
v___x_3662_ = 0;
v___x_3663_ = lean_box(0);
v___x_3664_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_3652_, v___x_3661_, v___x_3662_, v___x_3661_, v___x_3662_, v___x_3663_, v___f_3660_, v_cleanupAnnotations_3654_, v___y_3655_, v___y_3656_, v___y_3657_, v___y_3658_);
if (lean_obj_tag(v___x_3664_) == 0)
{
lean_object* v_a_3665_; lean_object* v___x_3667_; uint8_t v_isShared_3668_; uint8_t v_isSharedCheck_3672_; 
v_a_3665_ = lean_ctor_get(v___x_3664_, 0);
v_isSharedCheck_3672_ = !lean_is_exclusive(v___x_3664_);
if (v_isSharedCheck_3672_ == 0)
{
v___x_3667_ = v___x_3664_;
v_isShared_3668_ = v_isSharedCheck_3672_;
goto v_resetjp_3666_;
}
else
{
lean_inc(v_a_3665_);
lean_dec(v___x_3664_);
v___x_3667_ = lean_box(0);
v_isShared_3668_ = v_isSharedCheck_3672_;
goto v_resetjp_3666_;
}
v_resetjp_3666_:
{
lean_object* v___x_3670_; 
if (v_isShared_3668_ == 0)
{
v___x_3670_ = v___x_3667_;
goto v_reusejp_3669_;
}
else
{
lean_object* v_reuseFailAlloc_3671_; 
v_reuseFailAlloc_3671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3671_, 0, v_a_3665_);
v___x_3670_ = v_reuseFailAlloc_3671_;
goto v_reusejp_3669_;
}
v_reusejp_3669_:
{
return v___x_3670_;
}
}
}
else
{
lean_object* v_a_3673_; lean_object* v___x_3675_; uint8_t v_isShared_3676_; uint8_t v_isSharedCheck_3680_; 
v_a_3673_ = lean_ctor_get(v___x_3664_, 0);
v_isSharedCheck_3680_ = !lean_is_exclusive(v___x_3664_);
if (v_isSharedCheck_3680_ == 0)
{
v___x_3675_ = v___x_3664_;
v_isShared_3676_ = v_isSharedCheck_3680_;
goto v_resetjp_3674_;
}
else
{
lean_inc(v_a_3673_);
lean_dec(v___x_3664_);
v___x_3675_ = lean_box(0);
v_isShared_3676_ = v_isSharedCheck_3680_;
goto v_resetjp_3674_;
}
v_resetjp_3674_:
{
lean_object* v___x_3678_; 
if (v_isShared_3676_ == 0)
{
v___x_3678_ = v___x_3675_;
goto v_reusejp_3677_;
}
else
{
lean_object* v_reuseFailAlloc_3679_; 
v_reuseFailAlloc_3679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3679_, 0, v_a_3673_);
v___x_3678_ = v_reuseFailAlloc_3679_;
goto v_reusejp_3677_;
}
v_reusejp_3677_:
{
return v___x_3678_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__7___redArg___boxed(lean_object* v_e_3681_, lean_object* v_k_3682_, lean_object* v_cleanupAnnotations_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3689_; lean_object* v_res_3690_; 
v_cleanupAnnotations_boxed_3689_ = lean_unbox(v_cleanupAnnotations_3683_);
v_res_3690_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__7___redArg(v_e_3681_, v_k_3682_, v_cleanupAnnotations_boxed_3689_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_);
return v_res_3690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__7(lean_object* v_00_u03b1_3691_, lean_object* v_e_3692_, lean_object* v_k_3693_, uint8_t v_cleanupAnnotations_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_){
_start:
{
lean_object* v___x_3700_; 
v___x_3700_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__7___redArg(v_e_3692_, v_k_3693_, v_cleanupAnnotations_3694_, v___y_3695_, v___y_3696_, v___y_3697_, v___y_3698_);
return v___x_3700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__7___boxed(lean_object* v_00_u03b1_3701_, lean_object* v_e_3702_, lean_object* v_k_3703_, lean_object* v_cleanupAnnotations_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3710_; lean_object* v_res_3711_; 
v_cleanupAnnotations_boxed_3710_ = lean_unbox(v_cleanupAnnotations_3704_);
v_res_3711_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__7(v_00_u03b1_3701_, v_e_3702_, v_k_3703_, v_cleanupAnnotations_boxed_3710_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_);
return v_res_3711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0___redArg(lean_object* v_x_3712_, lean_object* v_x_3713_, lean_object* v_x_3714_){
_start:
{
if (lean_obj_tag(v_x_3712_) == 5)
{
lean_object* v_fn_3719_; lean_object* v_arg_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; 
v_fn_3719_ = lean_ctor_get(v_x_3712_, 0);
lean_inc_ref(v_fn_3719_);
v_arg_3720_ = lean_ctor_get(v_x_3712_, 1);
lean_inc_ref(v_arg_3720_);
lean_dec_ref(v_x_3712_);
v___x_3721_ = lean_array_set(v_x_3713_, v_x_3714_, v_arg_3720_);
v___x_3722_ = lean_unsigned_to_nat(1u);
v___x_3723_ = lean_nat_sub(v_x_3714_, v___x_3722_);
lean_dec(v_x_3714_);
v_x_3712_ = v_fn_3719_;
v_x_3713_ = v___x_3721_;
v_x_3714_ = v___x_3723_;
goto _start;
}
else
{
lean_object* v___x_3725_; uint8_t v___x_3726_; 
lean_dec(v_x_3714_);
v___x_3725_ = ((lean_object*)(l_Lean_Elab_WF_isWfParam_x3f___closed__1));
v___x_3726_ = l_Lean_Expr_isConstOf(v_x_3712_, v___x_3725_);
lean_dec_ref(v_x_3712_);
if (v___x_3726_ == 0)
{
lean_dec_ref(v_x_3713_);
goto v___jp_3716_;
}
else
{
lean_object* v___x_3727_; lean_object* v___x_3728_; uint8_t v___x_3729_; 
v___x_3727_ = lean_unsigned_to_nat(2u);
v___x_3728_ = lean_array_get_size(v_x_3713_);
v___x_3729_ = lean_nat_dec_le(v___x_3727_, v___x_3728_);
if (v___x_3729_ == 0)
{
lean_dec_ref(v_x_3713_);
goto v___jp_3716_;
}
else
{
lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; 
v___x_3730_ = lean_unsigned_to_nat(1u);
v___x_3731_ = lean_array_fget(v_x_3713_, v___x_3730_);
v___x_3732_ = l_Array_toSubarray___redArg(v_x_3713_, v___x_3727_, v___x_3728_);
v___x_3733_ = l_Subarray_copy___redArg(v___x_3732_);
v___x_3734_ = l_Lean_mkAppN(v___x_3731_, v___x_3733_);
lean_dec_ref(v___x_3733_);
v___x_3735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3735_, 0, v___x_3734_);
v___x_3736_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3736_, 0, v___x_3735_);
v___x_3737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3737_, 0, v___x_3736_);
return v___x_3737_;
}
}
}
v___jp_3716_:
{
lean_object* v___x_3717_; lean_object* v___x_3718_; 
v___x_3717_ = ((lean_object*)(l_Lean_Elab_WF_paramProj___closed__0));
v___x_3718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3718_, 0, v___x_3717_);
return v___x_3718_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0___redArg___boxed(lean_object* v_x_3738_, lean_object* v_x_3739_, lean_object* v_x_3740_, lean_object* v___y_3741_){
_start:
{
lean_object* v_res_3742_; 
v_res_3742_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0___redArg(v_x_3738_, v_x_3739_, v_x_3740_);
return v_res_3742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preprocess___lam__1(lean_object* v_e_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_){
_start:
{
lean_object* v_dummy_3749_; lean_object* v_nargs_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; 
v_dummy_3749_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0);
v_nargs_3750_ = l_Lean_Expr_getAppNumArgs(v_e_3743_);
lean_inc(v_nargs_3750_);
v___x_3751_ = lean_mk_array(v_nargs_3750_, v_dummy_3749_);
v___x_3752_ = lean_unsigned_to_nat(1u);
v___x_3753_ = lean_nat_sub(v_nargs_3750_, v___x_3752_);
lean_dec(v_nargs_3750_);
v___x_3754_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0___redArg(v_e_3743_, v___x_3751_, v___x_3753_);
return v___x_3754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preprocess___lam__1___boxed(lean_object* v_e_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_){
_start:
{
lean_object* v_res_3761_; 
v_res_3761_ = l_Lean_Elab_WF_preprocess___lam__1(v_e_3755_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_);
lean_dec(v___y_3759_);
lean_dec_ref(v___y_3758_);
lean_dec(v___y_3757_);
lean_dec_ref(v___y_3756_);
return v_res_3761_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__10_spec__12___redArg(lean_object* v_ref_3762_){
_start:
{
lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; 
v___x_3764_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__5);
v___x_3765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3765_, 0, v_ref_3762_);
lean_ctor_set(v___x_3765_, 1, v___x_3764_);
v___x_3766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3766_, 0, v___x_3765_);
return v___x_3766_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__10_spec__12___redArg___boxed(lean_object* v_ref_3767_, lean_object* v___y_3768_){
_start:
{
lean_object* v_res_3769_; 
v_res_3769_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__10_spec__12___redArg(v_ref_3767_);
return v_res_3769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__10___redArg(lean_object* v_x_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_){
_start:
{
lean_object* v___y_3778_; lean_object* v_fileName_3787_; lean_object* v_fileMap_3788_; lean_object* v_options_3789_; lean_object* v_currRecDepth_3790_; lean_object* v_maxRecDepth_3791_; lean_object* v_ref_3792_; lean_object* v_currNamespace_3793_; lean_object* v_openDecls_3794_; lean_object* v_initHeartbeats_3795_; lean_object* v_maxHeartbeats_3796_; lean_object* v_quotContext_3797_; lean_object* v_currMacroScope_3798_; uint8_t v_diag_3799_; lean_object* v_cancelTk_x3f_3800_; uint8_t v_suppressElabErrors_3801_; lean_object* v_inheritedTraceOptions_3802_; lean_object* v___x_3804_; uint8_t v_isShared_3805_; uint8_t v_isSharedCheck_3814_; 
v_fileName_3787_ = lean_ctor_get(v___y_3774_, 0);
v_fileMap_3788_ = lean_ctor_get(v___y_3774_, 1);
v_options_3789_ = lean_ctor_get(v___y_3774_, 2);
v_currRecDepth_3790_ = lean_ctor_get(v___y_3774_, 3);
v_maxRecDepth_3791_ = lean_ctor_get(v___y_3774_, 4);
v_ref_3792_ = lean_ctor_get(v___y_3774_, 5);
v_currNamespace_3793_ = lean_ctor_get(v___y_3774_, 6);
v_openDecls_3794_ = lean_ctor_get(v___y_3774_, 7);
v_initHeartbeats_3795_ = lean_ctor_get(v___y_3774_, 8);
v_maxHeartbeats_3796_ = lean_ctor_get(v___y_3774_, 9);
v_quotContext_3797_ = lean_ctor_get(v___y_3774_, 10);
v_currMacroScope_3798_ = lean_ctor_get(v___y_3774_, 11);
v_diag_3799_ = lean_ctor_get_uint8(v___y_3774_, sizeof(void*)*14);
v_cancelTk_x3f_3800_ = lean_ctor_get(v___y_3774_, 12);
v_suppressElabErrors_3801_ = lean_ctor_get_uint8(v___y_3774_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3802_ = lean_ctor_get(v___y_3774_, 13);
v_isSharedCheck_3814_ = !lean_is_exclusive(v___y_3774_);
if (v_isSharedCheck_3814_ == 0)
{
v___x_3804_ = v___y_3774_;
v_isShared_3805_ = v_isSharedCheck_3814_;
goto v_resetjp_3803_;
}
else
{
lean_inc(v_inheritedTraceOptions_3802_);
lean_inc(v_cancelTk_x3f_3800_);
lean_inc(v_currMacroScope_3798_);
lean_inc(v_quotContext_3797_);
lean_inc(v_maxHeartbeats_3796_);
lean_inc(v_initHeartbeats_3795_);
lean_inc(v_openDecls_3794_);
lean_inc(v_currNamespace_3793_);
lean_inc(v_ref_3792_);
lean_inc(v_maxRecDepth_3791_);
lean_inc(v_currRecDepth_3790_);
lean_inc(v_options_3789_);
lean_inc(v_fileMap_3788_);
lean_inc(v_fileName_3787_);
lean_dec(v___y_3774_);
v___x_3804_ = lean_box(0);
v_isShared_3805_ = v_isSharedCheck_3814_;
goto v_resetjp_3803_;
}
v___jp_3777_:
{
if (lean_obj_tag(v___y_3778_) == 0)
{
return v___y_3778_;
}
else
{
lean_object* v_a_3779_; lean_object* v___x_3781_; uint8_t v_isShared_3782_; uint8_t v_isSharedCheck_3786_; 
v_a_3779_ = lean_ctor_get(v___y_3778_, 0);
v_isSharedCheck_3786_ = !lean_is_exclusive(v___y_3778_);
if (v_isSharedCheck_3786_ == 0)
{
v___x_3781_ = v___y_3778_;
v_isShared_3782_ = v_isSharedCheck_3786_;
goto v_resetjp_3780_;
}
else
{
lean_inc(v_a_3779_);
lean_dec(v___y_3778_);
v___x_3781_ = lean_box(0);
v_isShared_3782_ = v_isSharedCheck_3786_;
goto v_resetjp_3780_;
}
v_resetjp_3780_:
{
lean_object* v___x_3784_; 
if (v_isShared_3782_ == 0)
{
v___x_3784_ = v___x_3781_;
goto v_reusejp_3783_;
}
else
{
lean_object* v_reuseFailAlloc_3785_; 
v_reuseFailAlloc_3785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3785_, 0, v_a_3779_);
v___x_3784_ = v_reuseFailAlloc_3785_;
goto v_reusejp_3783_;
}
v_reusejp_3783_:
{
return v___x_3784_;
}
}
}
}
v_resetjp_3803_:
{
uint8_t v___x_3806_; 
v___x_3806_ = lean_nat_dec_eq(v_currRecDepth_3790_, v_maxRecDepth_3791_);
if (v___x_3806_ == 0)
{
lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3810_; 
v___x_3807_ = lean_unsigned_to_nat(1u);
v___x_3808_ = lean_nat_add(v_currRecDepth_3790_, v___x_3807_);
lean_dec(v_currRecDepth_3790_);
if (v_isShared_3805_ == 0)
{
lean_ctor_set(v___x_3804_, 3, v___x_3808_);
v___x_3810_ = v___x_3804_;
goto v_reusejp_3809_;
}
else
{
lean_object* v_reuseFailAlloc_3812_; 
v_reuseFailAlloc_3812_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_3812_, 0, v_fileName_3787_);
lean_ctor_set(v_reuseFailAlloc_3812_, 1, v_fileMap_3788_);
lean_ctor_set(v_reuseFailAlloc_3812_, 2, v_options_3789_);
lean_ctor_set(v_reuseFailAlloc_3812_, 3, v___x_3808_);
lean_ctor_set(v_reuseFailAlloc_3812_, 4, v_maxRecDepth_3791_);
lean_ctor_set(v_reuseFailAlloc_3812_, 5, v_ref_3792_);
lean_ctor_set(v_reuseFailAlloc_3812_, 6, v_currNamespace_3793_);
lean_ctor_set(v_reuseFailAlloc_3812_, 7, v_openDecls_3794_);
lean_ctor_set(v_reuseFailAlloc_3812_, 8, v_initHeartbeats_3795_);
lean_ctor_set(v_reuseFailAlloc_3812_, 9, v_maxHeartbeats_3796_);
lean_ctor_set(v_reuseFailAlloc_3812_, 10, v_quotContext_3797_);
lean_ctor_set(v_reuseFailAlloc_3812_, 11, v_currMacroScope_3798_);
lean_ctor_set(v_reuseFailAlloc_3812_, 12, v_cancelTk_x3f_3800_);
lean_ctor_set(v_reuseFailAlloc_3812_, 13, v_inheritedTraceOptions_3802_);
lean_ctor_set_uint8(v_reuseFailAlloc_3812_, sizeof(void*)*14, v_diag_3799_);
lean_ctor_set_uint8(v_reuseFailAlloc_3812_, sizeof(void*)*14 + 1, v_suppressElabErrors_3801_);
v___x_3810_ = v_reuseFailAlloc_3812_;
goto v_reusejp_3809_;
}
v_reusejp_3809_:
{
lean_object* v___x_3811_; 
v___x_3811_ = lean_apply_6(v_x_3770_, v___y_3771_, v___y_3772_, v___y_3773_, v___x_3810_, v___y_3775_, lean_box(0));
v___y_3778_ = v___x_3811_;
goto v___jp_3777_;
}
}
else
{
lean_object* v___x_3813_; 
lean_del_object(v___x_3804_);
lean_dec_ref(v_inheritedTraceOptions_3802_);
lean_dec(v_cancelTk_x3f_3800_);
lean_dec(v_currMacroScope_3798_);
lean_dec(v_quotContext_3797_);
lean_dec(v_maxHeartbeats_3796_);
lean_dec(v_initHeartbeats_3795_);
lean_dec(v_openDecls_3794_);
lean_dec(v_currNamespace_3793_);
lean_dec(v_maxRecDepth_3791_);
lean_dec(v_currRecDepth_3790_);
lean_dec_ref(v_options_3789_);
lean_dec_ref(v_fileMap_3788_);
lean_dec_ref(v_fileName_3787_);
lean_dec(v___y_3775_);
lean_dec(v___y_3773_);
lean_dec_ref(v___y_3772_);
lean_dec(v___y_3771_);
lean_dec_ref(v_x_3770_);
v___x_3813_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__10_spec__12___redArg(v_ref_3792_);
v___y_3778_ = v___x_3813_;
goto v___jp_3777_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__10___redArg___boxed(lean_object* v_x_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_){
_start:
{
lean_object* v_res_3822_; 
v_res_3822_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__10___redArg(v_x_3815_, v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_, v___y_3820_);
return v_res_3822_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(lean_object* v_pre_3823_, lean_object* v_post_3824_, size_t v_sz_3825_, size_t v_i_3826_, lean_object* v_bs_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_){
_start:
{
uint8_t v___x_3834_; 
v___x_3834_ = lean_usize_dec_lt(v_i_3826_, v_sz_3825_);
if (v___x_3834_ == 0)
{
lean_object* v___x_3835_; 
lean_dec(v___y_3832_);
lean_dec_ref(v___y_3831_);
lean_dec(v___y_3830_);
lean_dec_ref(v___y_3829_);
lean_dec(v___y_3828_);
lean_dec_ref(v_post_3824_);
lean_dec_ref(v_pre_3823_);
v___x_3835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3835_, 0, v_bs_3827_);
return v___x_3835_;
}
else
{
lean_object* v_v_3836_; lean_object* v___x_3837_; 
v_v_3836_ = lean_array_uget_borrowed(v_bs_3827_, v_i_3826_);
lean_inc(v___y_3832_);
lean_inc_ref(v___y_3831_);
lean_inc(v___y_3830_);
lean_inc_ref(v___y_3829_);
lean_inc(v___y_3828_);
lean_inc(v_v_3836_);
lean_inc_ref(v_post_3824_);
lean_inc_ref(v_pre_3823_);
v___x_3837_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3823_, v_post_3824_, v_v_3836_, v___y_3828_, v___y_3829_, v___y_3830_, v___y_3831_, v___y_3832_);
if (lean_obj_tag(v___x_3837_) == 0)
{
lean_object* v_a_3838_; lean_object* v___x_3839_; lean_object* v_bs_x27_3840_; size_t v___x_3841_; size_t v___x_3842_; lean_object* v___x_3843_; 
v_a_3838_ = lean_ctor_get(v___x_3837_, 0);
lean_inc(v_a_3838_);
lean_dec_ref(v___x_3837_);
v___x_3839_ = lean_unsigned_to_nat(0u);
v_bs_x27_3840_ = lean_array_uset(v_bs_3827_, v_i_3826_, v___x_3839_);
v___x_3841_ = ((size_t)1ULL);
v___x_3842_ = lean_usize_add(v_i_3826_, v___x_3841_);
v___x_3843_ = lean_array_uset(v_bs_x27_3840_, v_i_3826_, v_a_3838_);
v_i_3826_ = v___x_3842_;
v_bs_3827_ = v___x_3843_;
goto _start;
}
else
{
lean_object* v_a_3845_; lean_object* v___x_3847_; uint8_t v_isShared_3848_; uint8_t v_isSharedCheck_3852_; 
lean_dec(v___y_3832_);
lean_dec_ref(v___y_3831_);
lean_dec(v___y_3830_);
lean_dec_ref(v___y_3829_);
lean_dec(v___y_3828_);
lean_dec_ref(v_bs_3827_);
lean_dec_ref(v_post_3824_);
lean_dec_ref(v_pre_3823_);
v_a_3845_ = lean_ctor_get(v___x_3837_, 0);
v_isSharedCheck_3852_ = !lean_is_exclusive(v___x_3837_);
if (v_isSharedCheck_3852_ == 0)
{
v___x_3847_ = v___x_3837_;
v_isShared_3848_ = v_isSharedCheck_3852_;
goto v_resetjp_3846_;
}
else
{
lean_inc(v_a_3845_);
lean_dec(v___x_3837_);
v___x_3847_ = lean_box(0);
v_isShared_3848_ = v_isSharedCheck_3852_;
goto v_resetjp_3846_;
}
v_resetjp_3846_:
{
lean_object* v___x_3850_; 
if (v_isShared_3848_ == 0)
{
v___x_3850_ = v___x_3847_;
goto v_reusejp_3849_;
}
else
{
lean_object* v_reuseFailAlloc_3851_; 
v_reuseFailAlloc_3851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3851_, 0, v_a_3845_);
v___x_3850_ = v_reuseFailAlloc_3851_;
goto v_reusejp_3849_;
}
v_reusejp_3849_:
{
return v___x_3850_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9(lean_object* v_pre_3853_, lean_object* v_post_3854_, lean_object* v_x_3855_, lean_object* v_x_3856_, lean_object* v_x_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_){
_start:
{
if (lean_obj_tag(v_x_3855_) == 5)
{
lean_object* v_fn_3864_; lean_object* v_arg_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; 
v_fn_3864_ = lean_ctor_get(v_x_3855_, 0);
lean_inc_ref(v_fn_3864_);
v_arg_3865_ = lean_ctor_get(v_x_3855_, 1);
lean_inc_ref(v_arg_3865_);
lean_dec_ref(v_x_3855_);
v___x_3866_ = lean_array_set(v_x_3856_, v_x_3857_, v_arg_3865_);
v___x_3867_ = lean_unsigned_to_nat(1u);
v___x_3868_ = lean_nat_sub(v_x_3857_, v___x_3867_);
lean_dec(v_x_3857_);
v_x_3855_ = v_fn_3864_;
v_x_3856_ = v___x_3866_;
v_x_3857_ = v___x_3868_;
goto _start;
}
else
{
lean_object* v___x_3870_; 
lean_dec(v_x_3857_);
lean_inc(v___y_3862_);
lean_inc_ref(v___y_3861_);
lean_inc(v___y_3860_);
lean_inc_ref(v___y_3859_);
lean_inc(v___y_3858_);
lean_inc_ref(v_post_3854_);
lean_inc_ref(v_pre_3853_);
v___x_3870_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3853_, v_post_3854_, v_x_3855_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_, v___y_3862_);
if (lean_obj_tag(v___x_3870_) == 0)
{
lean_object* v_a_3871_; size_t v_sz_3872_; size_t v___x_3873_; lean_object* v___x_3874_; 
v_a_3871_ = lean_ctor_get(v___x_3870_, 0);
lean_inc(v_a_3871_);
lean_dec_ref(v___x_3870_);
v_sz_3872_ = lean_array_size(v_x_3856_);
v___x_3873_ = ((size_t)0ULL);
lean_inc(v___y_3862_);
lean_inc_ref(v___y_3861_);
lean_inc(v___y_3860_);
lean_inc_ref(v___y_3859_);
lean_inc(v___y_3858_);
lean_inc_ref(v_post_3854_);
lean_inc_ref(v_pre_3853_);
v___x_3874_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3853_, v_post_3854_, v_sz_3872_, v___x_3873_, v_x_3856_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_, v___y_3862_);
if (lean_obj_tag(v___x_3874_) == 0)
{
lean_object* v_a_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; 
v_a_3875_ = lean_ctor_get(v___x_3874_, 0);
lean_inc(v_a_3875_);
lean_dec_ref(v___x_3874_);
v___x_3876_ = l_Lean_mkAppN(v_a_3871_, v_a_3875_);
lean_dec(v_a_3875_);
v___x_3877_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__8(v_pre_3853_, v_post_3854_, v___x_3876_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_, v___y_3862_);
return v___x_3877_;
}
else
{
lean_object* v_a_3878_; lean_object* v___x_3880_; uint8_t v_isShared_3881_; uint8_t v_isSharedCheck_3885_; 
lean_dec(v_a_3871_);
lean_dec(v___y_3862_);
lean_dec_ref(v___y_3861_);
lean_dec(v___y_3860_);
lean_dec_ref(v___y_3859_);
lean_dec(v___y_3858_);
lean_dec_ref(v_post_3854_);
lean_dec_ref(v_pre_3853_);
v_a_3878_ = lean_ctor_get(v___x_3874_, 0);
v_isSharedCheck_3885_ = !lean_is_exclusive(v___x_3874_);
if (v_isSharedCheck_3885_ == 0)
{
v___x_3880_ = v___x_3874_;
v_isShared_3881_ = v_isSharedCheck_3885_;
goto v_resetjp_3879_;
}
else
{
lean_inc(v_a_3878_);
lean_dec(v___x_3874_);
v___x_3880_ = lean_box(0);
v_isShared_3881_ = v_isSharedCheck_3885_;
goto v_resetjp_3879_;
}
v_resetjp_3879_:
{
lean_object* v___x_3883_; 
if (v_isShared_3881_ == 0)
{
v___x_3883_ = v___x_3880_;
goto v_reusejp_3882_;
}
else
{
lean_object* v_reuseFailAlloc_3884_; 
v_reuseFailAlloc_3884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3884_, 0, v_a_3878_);
v___x_3883_ = v_reuseFailAlloc_3884_;
goto v_reusejp_3882_;
}
v_reusejp_3882_:
{
return v___x_3883_;
}
}
}
}
else
{
lean_dec(v___y_3862_);
lean_dec_ref(v___y_3861_);
lean_dec(v___y_3860_);
lean_dec_ref(v___y_3859_);
lean_dec(v___y_3858_);
lean_dec_ref(v_x_3856_);
lean_dec_ref(v_post_3854_);
lean_dec_ref(v_pre_3853_);
return v___x_3870_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4___lam__1(lean_object* v_pre_3886_, lean_object* v_e_3887_, lean_object* v_post_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_){
_start:
{
lean_object* v___y_3896_; lean_object* v___y_3897_; lean_object* v___y_3898_; uint8_t v___y_3899_; lean_object* v___y_3900_; lean_object* v___y_3901_; lean_object* v___y_3902_; uint8_t v___y_3903_; uint8_t v___y_3913_; lean_object* v___y_3914_; lean_object* v___y_3915_; lean_object* v___y_3916_; lean_object* v___y_3917_; uint8_t v___y_3918_; lean_object* v___y_3926_; lean_object* v___y_3927_; uint8_t v___y_3928_; lean_object* v___y_3929_; lean_object* v___y_3930_; uint8_t v___y_3931_; lean_object* v___x_3938_; 
lean_inc_ref(v_pre_3886_);
lean_inc(v___y_3893_);
lean_inc_ref(v___y_3892_);
lean_inc(v___y_3891_);
lean_inc_ref(v___y_3890_);
lean_inc_ref(v_e_3887_);
v___x_3938_ = lean_apply_6(v_pre_3886_, v_e_3887_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_, lean_box(0));
if (lean_obj_tag(v___x_3938_) == 0)
{
lean_object* v_a_3939_; lean_object* v___x_3941_; uint8_t v_isShared_3942_; uint8_t v_isSharedCheck_4028_; 
v_a_3939_ = lean_ctor_get(v___x_3938_, 0);
v_isSharedCheck_4028_ = !lean_is_exclusive(v___x_3938_);
if (v_isSharedCheck_4028_ == 0)
{
v___x_3941_ = v___x_3938_;
v_isShared_3942_ = v_isSharedCheck_4028_;
goto v_resetjp_3940_;
}
else
{
lean_inc(v_a_3939_);
lean_dec(v___x_3938_);
v___x_3941_ = lean_box(0);
v_isShared_3942_ = v_isSharedCheck_4028_;
goto v_resetjp_3940_;
}
v_resetjp_3940_:
{
lean_object* v___y_3944_; 
switch(lean_obj_tag(v_a_3939_))
{
case 0:
{
lean_object* v_e_4018_; lean_object* v___x_4020_; 
lean_dec(v___y_3893_);
lean_dec_ref(v___y_3892_);
lean_dec(v___y_3891_);
lean_dec_ref(v___y_3890_);
lean_dec(v___y_3889_);
lean_dec_ref(v_post_3888_);
lean_dec_ref(v_e_3887_);
lean_dec_ref(v_pre_3886_);
v_e_4018_ = lean_ctor_get(v_a_3939_, 0);
lean_inc_ref(v_e_4018_);
lean_dec_ref(v_a_3939_);
if (v_isShared_3942_ == 0)
{
lean_ctor_set(v___x_3941_, 0, v_e_4018_);
v___x_4020_ = v___x_3941_;
goto v_reusejp_4019_;
}
else
{
lean_object* v_reuseFailAlloc_4021_; 
v_reuseFailAlloc_4021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4021_, 0, v_e_4018_);
v___x_4020_ = v_reuseFailAlloc_4021_;
goto v_reusejp_4019_;
}
v_reusejp_4019_:
{
return v___x_4020_;
}
}
case 1:
{
lean_object* v_e_4022_; lean_object* v___x_4023_; 
lean_del_object(v___x_3941_);
lean_dec_ref(v_e_3887_);
v_e_4022_ = lean_ctor_get(v_a_3939_, 0);
lean_inc_ref(v_e_4022_);
lean_dec_ref(v_a_3939_);
lean_inc(v___y_3893_);
lean_inc_ref(v___y_3892_);
lean_inc(v___y_3891_);
lean_inc_ref(v___y_3890_);
lean_inc(v___y_3889_);
lean_inc_ref(v_post_3888_);
lean_inc_ref(v_pre_3886_);
v___x_4023_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3886_, v_post_3888_, v_e_4022_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
if (lean_obj_tag(v___x_4023_) == 0)
{
lean_object* v_a_4024_; lean_object* v___x_4025_; 
v_a_4024_ = lean_ctor_get(v___x_4023_, 0);
lean_inc(v_a_4024_);
lean_dec_ref(v___x_4023_);
v___x_4025_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__8(v_pre_3886_, v_post_3888_, v_a_4024_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
return v___x_4025_;
}
else
{
lean_dec(v___y_3893_);
lean_dec_ref(v___y_3892_);
lean_dec(v___y_3891_);
lean_dec_ref(v___y_3890_);
lean_dec(v___y_3889_);
lean_dec_ref(v_post_3888_);
lean_dec_ref(v_pre_3886_);
return v___x_4023_;
}
}
default: 
{
lean_object* v_e_x3f_4026_; 
lean_del_object(v___x_3941_);
v_e_x3f_4026_ = lean_ctor_get(v_a_3939_, 0);
lean_inc(v_e_x3f_4026_);
lean_dec_ref(v_a_3939_);
if (lean_obj_tag(v_e_x3f_4026_) == 0)
{
v___y_3944_ = v_e_3887_;
goto v___jp_3943_;
}
else
{
lean_object* v_val_4027_; 
lean_dec_ref(v_e_3887_);
v_val_4027_ = lean_ctor_get(v_e_x3f_4026_, 0);
lean_inc(v_val_4027_);
lean_dec_ref(v_e_x3f_4026_);
v___y_3944_ = v_val_4027_;
goto v___jp_3943_;
}
}
}
v___jp_3943_:
{
switch(lean_obj_tag(v___y_3944_))
{
case 7:
{
lean_object* v_binderName_3945_; lean_object* v_binderType_3946_; lean_object* v_body_3947_; uint8_t v_binderInfo_3948_; lean_object* v___x_3949_; 
v_binderName_3945_ = lean_ctor_get(v___y_3944_, 0);
lean_inc(v_binderName_3945_);
v_binderType_3946_ = lean_ctor_get(v___y_3944_, 1);
v_body_3947_ = lean_ctor_get(v___y_3944_, 2);
v_binderInfo_3948_ = lean_ctor_get_uint8(v___y_3944_, sizeof(void*)*3 + 8);
lean_inc(v___y_3893_);
lean_inc_ref(v___y_3892_);
lean_inc(v___y_3891_);
lean_inc_ref(v___y_3890_);
lean_inc(v___y_3889_);
lean_inc_ref(v_binderType_3946_);
lean_inc_ref(v_post_3888_);
lean_inc_ref(v_pre_3886_);
v___x_3949_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3886_, v_post_3888_, v_binderType_3946_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
if (lean_obj_tag(v___x_3949_) == 0)
{
lean_object* v_a_3950_; lean_object* v___x_3951_; 
v_a_3950_ = lean_ctor_get(v___x_3949_, 0);
lean_inc(v_a_3950_);
lean_dec_ref(v___x_3949_);
lean_inc(v___y_3893_);
lean_inc_ref(v___y_3892_);
lean_inc(v___y_3891_);
lean_inc_ref(v___y_3890_);
lean_inc(v___y_3889_);
lean_inc_ref(v_body_3947_);
lean_inc_ref(v_post_3888_);
lean_inc_ref(v_pre_3886_);
v___x_3951_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3886_, v_post_3888_, v_body_3947_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
if (lean_obj_tag(v___x_3951_) == 0)
{
lean_object* v_a_3952_; size_t v___x_3953_; size_t v___x_3954_; uint8_t v___x_3955_; 
v_a_3952_ = lean_ctor_get(v___x_3951_, 0);
lean_inc(v_a_3952_);
lean_dec_ref(v___x_3951_);
v___x_3953_ = lean_ptr_addr(v_binderType_3946_);
v___x_3954_ = lean_ptr_addr(v_a_3950_);
v___x_3955_ = lean_usize_dec_eq(v___x_3953_, v___x_3954_);
if (v___x_3955_ == 0)
{
v___y_3926_ = v_a_3950_;
v___y_3927_ = v_a_3952_;
v___y_3928_ = v_binderInfo_3948_;
v___y_3929_ = v___y_3944_;
v___y_3930_ = v_binderName_3945_;
v___y_3931_ = v___x_3955_;
goto v___jp_3925_;
}
else
{
size_t v___x_3956_; size_t v___x_3957_; uint8_t v___x_3958_; 
v___x_3956_ = lean_ptr_addr(v_body_3947_);
v___x_3957_ = lean_ptr_addr(v_a_3952_);
v___x_3958_ = lean_usize_dec_eq(v___x_3956_, v___x_3957_);
v___y_3926_ = v_a_3950_;
v___y_3927_ = v_a_3952_;
v___y_3928_ = v_binderInfo_3948_;
v___y_3929_ = v___y_3944_;
v___y_3930_ = v_binderName_3945_;
v___y_3931_ = v___x_3958_;
goto v___jp_3925_;
}
}
else
{
lean_dec(v_a_3950_);
lean_dec_ref(v___y_3944_);
lean_dec(v_binderName_3945_);
lean_dec(v___y_3893_);
lean_dec_ref(v___y_3892_);
lean_dec(v___y_3891_);
lean_dec_ref(v___y_3890_);
lean_dec(v___y_3889_);
lean_dec_ref(v_post_3888_);
lean_dec_ref(v_pre_3886_);
return v___x_3951_;
}
}
else
{
lean_dec_ref(v___y_3944_);
lean_dec(v_binderName_3945_);
lean_dec(v___y_3893_);
lean_dec_ref(v___y_3892_);
lean_dec(v___y_3891_);
lean_dec_ref(v___y_3890_);
lean_dec(v___y_3889_);
lean_dec_ref(v_post_3888_);
lean_dec_ref(v_pre_3886_);
return v___x_3949_;
}
}
case 6:
{
lean_object* v_binderName_3959_; lean_object* v_binderType_3960_; lean_object* v_body_3961_; uint8_t v_binderInfo_3962_; lean_object* v___x_3963_; 
v_binderName_3959_ = lean_ctor_get(v___y_3944_, 0);
lean_inc(v_binderName_3959_);
v_binderType_3960_ = lean_ctor_get(v___y_3944_, 1);
v_body_3961_ = lean_ctor_get(v___y_3944_, 2);
v_binderInfo_3962_ = lean_ctor_get_uint8(v___y_3944_, sizeof(void*)*3 + 8);
lean_inc(v___y_3893_);
lean_inc_ref(v___y_3892_);
lean_inc(v___y_3891_);
lean_inc_ref(v___y_3890_);
lean_inc(v___y_3889_);
lean_inc_ref(v_binderType_3960_);
lean_inc_ref(v_post_3888_);
lean_inc_ref(v_pre_3886_);
v___x_3963_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3886_, v_post_3888_, v_binderType_3960_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
if (lean_obj_tag(v___x_3963_) == 0)
{
lean_object* v_a_3964_; lean_object* v___x_3965_; 
v_a_3964_ = lean_ctor_get(v___x_3963_, 0);
lean_inc(v_a_3964_);
lean_dec_ref(v___x_3963_);
lean_inc(v___y_3893_);
lean_inc_ref(v___y_3892_);
lean_inc(v___y_3891_);
lean_inc_ref(v___y_3890_);
lean_inc(v___y_3889_);
lean_inc_ref(v_body_3961_);
lean_inc_ref(v_post_3888_);
lean_inc_ref(v_pre_3886_);
v___x_3965_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3886_, v_post_3888_, v_body_3961_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
if (lean_obj_tag(v___x_3965_) == 0)
{
lean_object* v_a_3966_; size_t v___x_3967_; size_t v___x_3968_; uint8_t v___x_3969_; 
v_a_3966_ = lean_ctor_get(v___x_3965_, 0);
lean_inc(v_a_3966_);
lean_dec_ref(v___x_3965_);
v___x_3967_ = lean_ptr_addr(v_binderType_3960_);
v___x_3968_ = lean_ptr_addr(v_a_3964_);
v___x_3969_ = lean_usize_dec_eq(v___x_3967_, v___x_3968_);
if (v___x_3969_ == 0)
{
v___y_3913_ = v_binderInfo_3962_;
v___y_3914_ = v_a_3964_;
v___y_3915_ = v_binderName_3959_;
v___y_3916_ = v_a_3966_;
v___y_3917_ = v___y_3944_;
v___y_3918_ = v___x_3969_;
goto v___jp_3912_;
}
else
{
size_t v___x_3970_; size_t v___x_3971_; uint8_t v___x_3972_; 
v___x_3970_ = lean_ptr_addr(v_body_3961_);
v___x_3971_ = lean_ptr_addr(v_a_3966_);
v___x_3972_ = lean_usize_dec_eq(v___x_3970_, v___x_3971_);
v___y_3913_ = v_binderInfo_3962_;
v___y_3914_ = v_a_3964_;
v___y_3915_ = v_binderName_3959_;
v___y_3916_ = v_a_3966_;
v___y_3917_ = v___y_3944_;
v___y_3918_ = v___x_3972_;
goto v___jp_3912_;
}
}
else
{
lean_dec(v_a_3964_);
lean_dec_ref(v___y_3944_);
lean_dec(v_binderName_3959_);
lean_dec(v___y_3893_);
lean_dec_ref(v___y_3892_);
lean_dec(v___y_3891_);
lean_dec_ref(v___y_3890_);
lean_dec(v___y_3889_);
lean_dec_ref(v_post_3888_);
lean_dec_ref(v_pre_3886_);
return v___x_3965_;
}
}
else
{
lean_dec_ref(v___y_3944_);
lean_dec(v_binderName_3959_);
lean_dec(v___y_3893_);
lean_dec_ref(v___y_3892_);
lean_dec(v___y_3891_);
lean_dec_ref(v___y_3890_);
lean_dec(v___y_3889_);
lean_dec_ref(v_post_3888_);
lean_dec_ref(v_pre_3886_);
return v___x_3963_;
}
}
case 8:
{
lean_object* v_declName_3973_; lean_object* v_type_3974_; lean_object* v_value_3975_; lean_object* v_body_3976_; uint8_t v_nondep_3977_; lean_object* v___x_3978_; 
v_declName_3973_ = lean_ctor_get(v___y_3944_, 0);
lean_inc(v_declName_3973_);
v_type_3974_ = lean_ctor_get(v___y_3944_, 1);
v_value_3975_ = lean_ctor_get(v___y_3944_, 2);
v_body_3976_ = lean_ctor_get(v___y_3944_, 3);
lean_inc_ref(v_body_3976_);
v_nondep_3977_ = lean_ctor_get_uint8(v___y_3944_, sizeof(void*)*4 + 8);
lean_inc(v___y_3893_);
lean_inc_ref(v___y_3892_);
lean_inc(v___y_3891_);
lean_inc_ref(v___y_3890_);
lean_inc(v___y_3889_);
lean_inc_ref(v_type_3974_);
lean_inc_ref(v_post_3888_);
lean_inc_ref(v_pre_3886_);
v___x_3978_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3886_, v_post_3888_, v_type_3974_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
if (lean_obj_tag(v___x_3978_) == 0)
{
lean_object* v_a_3979_; lean_object* v___x_3980_; 
v_a_3979_ = lean_ctor_get(v___x_3978_, 0);
lean_inc(v_a_3979_);
lean_dec_ref(v___x_3978_);
lean_inc(v___y_3893_);
lean_inc_ref(v___y_3892_);
lean_inc(v___y_3891_);
lean_inc_ref(v___y_3890_);
lean_inc(v___y_3889_);
lean_inc_ref(v_value_3975_);
lean_inc_ref(v_post_3888_);
lean_inc_ref(v_pre_3886_);
v___x_3980_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3886_, v_post_3888_, v_value_3975_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
if (lean_obj_tag(v___x_3980_) == 0)
{
lean_object* v_a_3981_; lean_object* v___x_3982_; 
v_a_3981_ = lean_ctor_get(v___x_3980_, 0);
lean_inc(v_a_3981_);
lean_dec_ref(v___x_3980_);
lean_inc(v___y_3893_);
lean_inc_ref(v___y_3892_);
lean_inc(v___y_3891_);
lean_inc_ref(v___y_3890_);
lean_inc(v___y_3889_);
lean_inc_ref(v_body_3976_);
lean_inc_ref(v_post_3888_);
lean_inc_ref(v_pre_3886_);
v___x_3982_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3886_, v_post_3888_, v_body_3976_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
if (lean_obj_tag(v___x_3982_) == 0)
{
lean_object* v_a_3983_; size_t v___x_3984_; size_t v___x_3985_; uint8_t v___x_3986_; 
v_a_3983_ = lean_ctor_get(v___x_3982_, 0);
lean_inc(v_a_3983_);
lean_dec_ref(v___x_3982_);
v___x_3984_ = lean_ptr_addr(v_type_3974_);
v___x_3985_ = lean_ptr_addr(v_a_3979_);
v___x_3986_ = lean_usize_dec_eq(v___x_3984_, v___x_3985_);
if (v___x_3986_ == 0)
{
v___y_3896_ = v_body_3976_;
v___y_3897_ = v_declName_3973_;
v___y_3898_ = v_a_3979_;
v___y_3899_ = v_nondep_3977_;
v___y_3900_ = v_a_3983_;
v___y_3901_ = v_a_3981_;
v___y_3902_ = v___y_3944_;
v___y_3903_ = v___x_3986_;
goto v___jp_3895_;
}
else
{
size_t v___x_3987_; size_t v___x_3988_; uint8_t v___x_3989_; 
v___x_3987_ = lean_ptr_addr(v_value_3975_);
v___x_3988_ = lean_ptr_addr(v_a_3981_);
v___x_3989_ = lean_usize_dec_eq(v___x_3987_, v___x_3988_);
v___y_3896_ = v_body_3976_;
v___y_3897_ = v_declName_3973_;
v___y_3898_ = v_a_3979_;
v___y_3899_ = v_nondep_3977_;
v___y_3900_ = v_a_3983_;
v___y_3901_ = v_a_3981_;
v___y_3902_ = v___y_3944_;
v___y_3903_ = v___x_3989_;
goto v___jp_3895_;
}
}
else
{
lean_dec(v_a_3981_);
lean_dec(v_a_3979_);
lean_dec_ref(v_body_3976_);
lean_dec(v_declName_3973_);
lean_dec_ref(v___y_3944_);
lean_dec(v___y_3893_);
lean_dec_ref(v___y_3892_);
lean_dec(v___y_3891_);
lean_dec_ref(v___y_3890_);
lean_dec(v___y_3889_);
lean_dec_ref(v_post_3888_);
lean_dec_ref(v_pre_3886_);
return v___x_3982_;
}
}
else
{
lean_dec(v_a_3979_);
lean_dec_ref(v_body_3976_);
lean_dec(v_declName_3973_);
lean_dec_ref(v___y_3944_);
lean_dec(v___y_3893_);
lean_dec_ref(v___y_3892_);
lean_dec(v___y_3891_);
lean_dec_ref(v___y_3890_);
lean_dec(v___y_3889_);
lean_dec_ref(v_post_3888_);
lean_dec_ref(v_pre_3886_);
return v___x_3980_;
}
}
else
{
lean_dec_ref(v_body_3976_);
lean_dec_ref(v___y_3944_);
lean_dec(v_declName_3973_);
lean_dec(v___y_3893_);
lean_dec_ref(v___y_3892_);
lean_dec(v___y_3891_);
lean_dec_ref(v___y_3890_);
lean_dec(v___y_3889_);
lean_dec_ref(v_post_3888_);
lean_dec_ref(v_pre_3886_);
return v___x_3978_;
}
}
case 5:
{
lean_object* v_dummy_3990_; lean_object* v_nargs_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; 
v_dummy_3990_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0);
v_nargs_3991_ = l_Lean_Expr_getAppNumArgs(v___y_3944_);
lean_inc(v_nargs_3991_);
v___x_3992_ = lean_mk_array(v_nargs_3991_, v_dummy_3990_);
v___x_3993_ = lean_unsigned_to_nat(1u);
v___x_3994_ = lean_nat_sub(v_nargs_3991_, v___x_3993_);
lean_dec(v_nargs_3991_);
v___x_3995_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9(v_pre_3886_, v_post_3888_, v___y_3944_, v___x_3992_, v___x_3994_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
return v___x_3995_;
}
case 10:
{
lean_object* v_data_3996_; lean_object* v_expr_3997_; lean_object* v___x_3998_; 
v_data_3996_ = lean_ctor_get(v___y_3944_, 0);
v_expr_3997_ = lean_ctor_get(v___y_3944_, 1);
lean_inc(v___y_3893_);
lean_inc_ref(v___y_3892_);
lean_inc(v___y_3891_);
lean_inc_ref(v___y_3890_);
lean_inc(v___y_3889_);
lean_inc_ref(v_expr_3997_);
lean_inc_ref(v_post_3888_);
lean_inc_ref(v_pre_3886_);
v___x_3998_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3886_, v_post_3888_, v_expr_3997_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
if (lean_obj_tag(v___x_3998_) == 0)
{
lean_object* v_a_3999_; size_t v___x_4000_; size_t v___x_4001_; uint8_t v___x_4002_; 
v_a_3999_ = lean_ctor_get(v___x_3998_, 0);
lean_inc(v_a_3999_);
lean_dec_ref(v___x_3998_);
v___x_4000_ = lean_ptr_addr(v_expr_3997_);
v___x_4001_ = lean_ptr_addr(v_a_3999_);
v___x_4002_ = lean_usize_dec_eq(v___x_4000_, v___x_4001_);
if (v___x_4002_ == 0)
{
lean_object* v___x_4003_; lean_object* v___x_4004_; 
lean_inc(v_data_3996_);
lean_dec_ref(v___y_3944_);
v___x_4003_ = l_Lean_Expr_mdata___override(v_data_3996_, v_a_3999_);
v___x_4004_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__8(v_pre_3886_, v_post_3888_, v___x_4003_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
return v___x_4004_;
}
else
{
lean_object* v___x_4005_; 
lean_dec(v_a_3999_);
v___x_4005_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__8(v_pre_3886_, v_post_3888_, v___y_3944_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
return v___x_4005_;
}
}
else
{
lean_dec_ref(v___y_3944_);
lean_dec(v___y_3893_);
lean_dec_ref(v___y_3892_);
lean_dec(v___y_3891_);
lean_dec_ref(v___y_3890_);
lean_dec(v___y_3889_);
lean_dec_ref(v_post_3888_);
lean_dec_ref(v_pre_3886_);
return v___x_3998_;
}
}
case 11:
{
lean_object* v_typeName_4006_; lean_object* v_idx_4007_; lean_object* v_struct_4008_; lean_object* v___x_4009_; 
v_typeName_4006_ = lean_ctor_get(v___y_3944_, 0);
v_idx_4007_ = lean_ctor_get(v___y_3944_, 1);
v_struct_4008_ = lean_ctor_get(v___y_3944_, 2);
lean_inc(v___y_3893_);
lean_inc_ref(v___y_3892_);
lean_inc(v___y_3891_);
lean_inc_ref(v___y_3890_);
lean_inc(v___y_3889_);
lean_inc_ref(v_struct_4008_);
lean_inc_ref(v_post_3888_);
lean_inc_ref(v_pre_3886_);
v___x_4009_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3886_, v_post_3888_, v_struct_4008_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
if (lean_obj_tag(v___x_4009_) == 0)
{
lean_object* v_a_4010_; size_t v___x_4011_; size_t v___x_4012_; uint8_t v___x_4013_; 
v_a_4010_ = lean_ctor_get(v___x_4009_, 0);
lean_inc(v_a_4010_);
lean_dec_ref(v___x_4009_);
v___x_4011_ = lean_ptr_addr(v_struct_4008_);
v___x_4012_ = lean_ptr_addr(v_a_4010_);
v___x_4013_ = lean_usize_dec_eq(v___x_4011_, v___x_4012_);
if (v___x_4013_ == 0)
{
lean_object* v___x_4014_; lean_object* v___x_4015_; 
lean_inc(v_idx_4007_);
lean_inc(v_typeName_4006_);
lean_dec_ref(v___y_3944_);
v___x_4014_ = l_Lean_Expr_proj___override(v_typeName_4006_, v_idx_4007_, v_a_4010_);
v___x_4015_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__8(v_pre_3886_, v_post_3888_, v___x_4014_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
return v___x_4015_;
}
else
{
lean_object* v___x_4016_; 
lean_dec(v_a_4010_);
v___x_4016_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__8(v_pre_3886_, v_post_3888_, v___y_3944_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
return v___x_4016_;
}
}
else
{
lean_dec_ref(v___y_3944_);
lean_dec(v___y_3893_);
lean_dec_ref(v___y_3892_);
lean_dec(v___y_3891_);
lean_dec_ref(v___y_3890_);
lean_dec(v___y_3889_);
lean_dec_ref(v_post_3888_);
lean_dec_ref(v_pre_3886_);
return v___x_4009_;
}
}
default: 
{
lean_object* v___x_4017_; 
v___x_4017_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__8(v_pre_3886_, v_post_3888_, v___y_3944_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
return v___x_4017_;
}
}
}
}
}
else
{
lean_object* v_a_4029_; lean_object* v___x_4031_; uint8_t v_isShared_4032_; uint8_t v_isSharedCheck_4036_; 
lean_dec(v___y_3893_);
lean_dec_ref(v___y_3892_);
lean_dec(v___y_3891_);
lean_dec_ref(v___y_3890_);
lean_dec(v___y_3889_);
lean_dec_ref(v_post_3888_);
lean_dec_ref(v_e_3887_);
lean_dec_ref(v_pre_3886_);
v_a_4029_ = lean_ctor_get(v___x_3938_, 0);
v_isSharedCheck_4036_ = !lean_is_exclusive(v___x_3938_);
if (v_isSharedCheck_4036_ == 0)
{
v___x_4031_ = v___x_3938_;
v_isShared_4032_ = v_isSharedCheck_4036_;
goto v_resetjp_4030_;
}
else
{
lean_inc(v_a_4029_);
lean_dec(v___x_3938_);
v___x_4031_ = lean_box(0);
v_isShared_4032_ = v_isSharedCheck_4036_;
goto v_resetjp_4030_;
}
v_resetjp_4030_:
{
lean_object* v___x_4034_; 
if (v_isShared_4032_ == 0)
{
v___x_4034_ = v___x_4031_;
goto v_reusejp_4033_;
}
else
{
lean_object* v_reuseFailAlloc_4035_; 
v_reuseFailAlloc_4035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4035_, 0, v_a_4029_);
v___x_4034_ = v_reuseFailAlloc_4035_;
goto v_reusejp_4033_;
}
v_reusejp_4033_:
{
return v___x_4034_;
}
}
}
v___jp_3895_:
{
if (v___y_3903_ == 0)
{
lean_object* v___x_3904_; lean_object* v___x_3905_; 
lean_dec_ref(v___y_3902_);
lean_dec_ref(v___y_3896_);
v___x_3904_ = l_Lean_Expr_letE___override(v___y_3897_, v___y_3898_, v___y_3901_, v___y_3900_, v___y_3899_);
v___x_3905_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__8(v_pre_3886_, v_post_3888_, v___x_3904_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
return v___x_3905_;
}
else
{
size_t v___x_3906_; size_t v___x_3907_; uint8_t v___x_3908_; 
v___x_3906_ = lean_ptr_addr(v___y_3896_);
lean_dec_ref(v___y_3896_);
v___x_3907_ = lean_ptr_addr(v___y_3900_);
v___x_3908_ = lean_usize_dec_eq(v___x_3906_, v___x_3907_);
if (v___x_3908_ == 0)
{
lean_object* v___x_3909_; lean_object* v___x_3910_; 
lean_dec_ref(v___y_3902_);
v___x_3909_ = l_Lean_Expr_letE___override(v___y_3897_, v___y_3898_, v___y_3901_, v___y_3900_, v___y_3899_);
v___x_3910_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__8(v_pre_3886_, v_post_3888_, v___x_3909_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
return v___x_3910_;
}
else
{
lean_object* v___x_3911_; 
lean_dec_ref(v___y_3901_);
lean_dec_ref(v___y_3900_);
lean_dec_ref(v___y_3898_);
lean_dec(v___y_3897_);
v___x_3911_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__8(v_pre_3886_, v_post_3888_, v___y_3902_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
return v___x_3911_;
}
}
}
v___jp_3912_:
{
if (v___y_3918_ == 0)
{
lean_object* v___x_3919_; lean_object* v___x_3920_; 
lean_dec_ref(v___y_3917_);
v___x_3919_ = l_Lean_Expr_lam___override(v___y_3915_, v___y_3914_, v___y_3916_, v___y_3913_);
v___x_3920_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__8(v_pre_3886_, v_post_3888_, v___x_3919_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
return v___x_3920_;
}
else
{
uint8_t v___x_3921_; 
v___x_3921_ = l_Lean_instBEqBinderInfo_beq(v___y_3913_, v___y_3913_);
if (v___x_3921_ == 0)
{
lean_object* v___x_3922_; lean_object* v___x_3923_; 
lean_dec_ref(v___y_3917_);
v___x_3922_ = l_Lean_Expr_lam___override(v___y_3915_, v___y_3914_, v___y_3916_, v___y_3913_);
v___x_3923_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__8(v_pre_3886_, v_post_3888_, v___x_3922_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
return v___x_3923_;
}
else
{
lean_object* v___x_3924_; 
lean_dec_ref(v___y_3916_);
lean_dec(v___y_3915_);
lean_dec_ref(v___y_3914_);
v___x_3924_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__8(v_pre_3886_, v_post_3888_, v___y_3917_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
return v___x_3924_;
}
}
}
v___jp_3925_:
{
if (v___y_3931_ == 0)
{
lean_object* v___x_3932_; lean_object* v___x_3933_; 
lean_dec_ref(v___y_3929_);
v___x_3932_ = l_Lean_Expr_forallE___override(v___y_3930_, v___y_3926_, v___y_3927_, v___y_3928_);
v___x_3933_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__8(v_pre_3886_, v_post_3888_, v___x_3932_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
return v___x_3933_;
}
else
{
uint8_t v___x_3934_; 
v___x_3934_ = l_Lean_instBEqBinderInfo_beq(v___y_3928_, v___y_3928_);
if (v___x_3934_ == 0)
{
lean_object* v___x_3935_; lean_object* v___x_3936_; 
lean_dec_ref(v___y_3929_);
v___x_3935_ = l_Lean_Expr_forallE___override(v___y_3930_, v___y_3926_, v___y_3927_, v___y_3928_);
v___x_3936_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__8(v_pre_3886_, v_post_3888_, v___x_3935_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
return v___x_3936_;
}
else
{
lean_object* v___x_3937_; 
lean_dec(v___y_3930_);
lean_dec_ref(v___y_3927_);
lean_dec_ref(v___y_3926_);
v___x_3937_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__8(v_pre_3886_, v_post_3888_, v___y_3929_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
return v___x_3937_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4___lam__1___boxed(lean_object* v_pre_4037_, lean_object* v_e_4038_, lean_object* v_post_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_){
_start:
{
lean_object* v_res_4046_; 
v_res_4046_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4___lam__1(v_pre_4037_, v_e_4038_, v_post_4039_, v___y_4040_, v___y_4041_, v___y_4042_, v___y_4043_, v___y_4044_);
return v_res_4046_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(lean_object* v_pre_4047_, lean_object* v_post_4048_, lean_object* v_e_4049_, lean_object* v_a_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_){
_start:
{
lean_object* v___x_4056_; lean_object* v___x_4057_; 
lean_inc(v_a_4050_);
v___x_4056_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_4056_, 0, lean_box(0));
lean_closure_set(v___x_4056_, 1, lean_box(0));
lean_closure_set(v___x_4056_, 2, v_a_4050_);
v___x_4057_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__0(lean_box(0), v___x_4056_, v___y_4051_, v___y_4052_, v___y_4053_, v___y_4054_);
if (lean_obj_tag(v___x_4057_) == 0)
{
lean_object* v_a_4058_; lean_object* v___x_4060_; uint8_t v_isShared_4061_; uint8_t v_isSharedCheck_4088_; 
v_a_4058_ = lean_ctor_get(v___x_4057_, 0);
v_isSharedCheck_4088_ = !lean_is_exclusive(v___x_4057_);
if (v_isSharedCheck_4088_ == 0)
{
v___x_4060_ = v___x_4057_;
v_isShared_4061_ = v_isSharedCheck_4088_;
goto v_resetjp_4059_;
}
else
{
lean_inc(v_a_4058_);
lean_dec(v___x_4057_);
v___x_4060_ = lean_box(0);
v_isShared_4061_ = v_isSharedCheck_4088_;
goto v_resetjp_4059_;
}
v_resetjp_4059_:
{
lean_object* v___x_4062_; 
v___x_4062_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___redArg(v_a_4058_, v_e_4049_);
lean_dec(v_a_4058_);
if (lean_obj_tag(v___x_4062_) == 0)
{
lean_object* v___f_4063_; lean_object* v___x_4064_; 
lean_del_object(v___x_4060_);
lean_inc_ref(v_e_4049_);
v___f_4063_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4___lam__1___boxed), 9, 3);
lean_closure_set(v___f_4063_, 0, v_pre_4047_);
lean_closure_set(v___f_4063_, 1, v_e_4049_);
lean_closure_set(v___f_4063_, 2, v_post_4048_);
lean_inc(v___y_4054_);
lean_inc_ref(v___y_4053_);
lean_inc(v___y_4052_);
lean_inc_ref(v___y_4051_);
lean_inc(v_a_4050_);
v___x_4064_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__10___redArg(v___f_4063_, v_a_4050_, v___y_4051_, v___y_4052_, v___y_4053_, v___y_4054_);
if (lean_obj_tag(v___x_4064_) == 0)
{
lean_object* v_a_4065_; lean_object* v___f_4066_; lean_object* v___x_4067_; 
v_a_4065_ = lean_ctor_get(v___x_4064_, 0);
lean_inc(v_a_4065_);
lean_dec_ref(v___x_4064_);
lean_inc(v_a_4065_);
v___f_4066_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__2___boxed), 4, 3);
lean_closure_set(v___f_4066_, 0, v_a_4050_);
lean_closure_set(v___f_4066_, 1, v_e_4049_);
lean_closure_set(v___f_4066_, 2, v_a_4065_);
v___x_4067_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__0(lean_box(0), v___f_4066_, v___y_4051_, v___y_4052_, v___y_4053_, v___y_4054_);
lean_dec(v___y_4054_);
lean_dec_ref(v___y_4053_);
lean_dec(v___y_4052_);
lean_dec_ref(v___y_4051_);
if (lean_obj_tag(v___x_4067_) == 0)
{
lean_object* v___x_4069_; uint8_t v_isShared_4070_; uint8_t v_isSharedCheck_4074_; 
v_isSharedCheck_4074_ = !lean_is_exclusive(v___x_4067_);
if (v_isSharedCheck_4074_ == 0)
{
lean_object* v_unused_4075_; 
v_unused_4075_ = lean_ctor_get(v___x_4067_, 0);
lean_dec(v_unused_4075_);
v___x_4069_ = v___x_4067_;
v_isShared_4070_ = v_isSharedCheck_4074_;
goto v_resetjp_4068_;
}
else
{
lean_dec(v___x_4067_);
v___x_4069_ = lean_box(0);
v_isShared_4070_ = v_isSharedCheck_4074_;
goto v_resetjp_4068_;
}
v_resetjp_4068_:
{
lean_object* v___x_4072_; 
if (v_isShared_4070_ == 0)
{
lean_ctor_set(v___x_4069_, 0, v_a_4065_);
v___x_4072_ = v___x_4069_;
goto v_reusejp_4071_;
}
else
{
lean_object* v_reuseFailAlloc_4073_; 
v_reuseFailAlloc_4073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4073_, 0, v_a_4065_);
v___x_4072_ = v_reuseFailAlloc_4073_;
goto v_reusejp_4071_;
}
v_reusejp_4071_:
{
return v___x_4072_;
}
}
}
else
{
lean_object* v_a_4076_; lean_object* v___x_4078_; uint8_t v_isShared_4079_; uint8_t v_isSharedCheck_4083_; 
lean_dec(v_a_4065_);
v_a_4076_ = lean_ctor_get(v___x_4067_, 0);
v_isSharedCheck_4083_ = !lean_is_exclusive(v___x_4067_);
if (v_isSharedCheck_4083_ == 0)
{
v___x_4078_ = v___x_4067_;
v_isShared_4079_ = v_isSharedCheck_4083_;
goto v_resetjp_4077_;
}
else
{
lean_inc(v_a_4076_);
lean_dec(v___x_4067_);
v___x_4078_ = lean_box(0);
v_isShared_4079_ = v_isSharedCheck_4083_;
goto v_resetjp_4077_;
}
v_resetjp_4077_:
{
lean_object* v___x_4081_; 
if (v_isShared_4079_ == 0)
{
v___x_4081_ = v___x_4078_;
goto v_reusejp_4080_;
}
else
{
lean_object* v_reuseFailAlloc_4082_; 
v_reuseFailAlloc_4082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4082_, 0, v_a_4076_);
v___x_4081_ = v_reuseFailAlloc_4082_;
goto v_reusejp_4080_;
}
v_reusejp_4080_:
{
return v___x_4081_;
}
}
}
}
else
{
lean_dec(v___y_4054_);
lean_dec_ref(v___y_4053_);
lean_dec(v___y_4052_);
lean_dec_ref(v___y_4051_);
lean_dec(v_a_4050_);
lean_dec_ref(v_e_4049_);
return v___x_4064_;
}
}
else
{
lean_object* v_val_4084_; lean_object* v___x_4086_; 
lean_dec(v___y_4054_);
lean_dec_ref(v___y_4053_);
lean_dec(v___y_4052_);
lean_dec_ref(v___y_4051_);
lean_dec(v_a_4050_);
lean_dec_ref(v_e_4049_);
lean_dec_ref(v_post_4048_);
lean_dec_ref(v_pre_4047_);
v_val_4084_ = lean_ctor_get(v___x_4062_, 0);
lean_inc(v_val_4084_);
lean_dec_ref(v___x_4062_);
if (v_isShared_4061_ == 0)
{
lean_ctor_set(v___x_4060_, 0, v_val_4084_);
v___x_4086_ = v___x_4060_;
goto v_reusejp_4085_;
}
else
{
lean_object* v_reuseFailAlloc_4087_; 
v_reuseFailAlloc_4087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4087_, 0, v_val_4084_);
v___x_4086_ = v_reuseFailAlloc_4087_;
goto v_reusejp_4085_;
}
v_reusejp_4085_:
{
return v___x_4086_;
}
}
}
}
else
{
lean_object* v_a_4089_; lean_object* v___x_4091_; uint8_t v_isShared_4092_; uint8_t v_isSharedCheck_4096_; 
lean_dec(v___y_4054_);
lean_dec_ref(v___y_4053_);
lean_dec(v___y_4052_);
lean_dec_ref(v___y_4051_);
lean_dec(v_a_4050_);
lean_dec_ref(v_e_4049_);
lean_dec_ref(v_post_4048_);
lean_dec_ref(v_pre_4047_);
v_a_4089_ = lean_ctor_get(v___x_4057_, 0);
v_isSharedCheck_4096_ = !lean_is_exclusive(v___x_4057_);
if (v_isSharedCheck_4096_ == 0)
{
v___x_4091_ = v___x_4057_;
v_isShared_4092_ = v_isSharedCheck_4096_;
goto v_resetjp_4090_;
}
else
{
lean_inc(v_a_4089_);
lean_dec(v___x_4057_);
v___x_4091_ = lean_box(0);
v_isShared_4092_ = v_isSharedCheck_4096_;
goto v_resetjp_4090_;
}
v_resetjp_4090_:
{
lean_object* v___x_4094_; 
if (v_isShared_4092_ == 0)
{
v___x_4094_ = v___x_4091_;
goto v_reusejp_4093_;
}
else
{
lean_object* v_reuseFailAlloc_4095_; 
v_reuseFailAlloc_4095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4095_, 0, v_a_4089_);
v___x_4094_ = v_reuseFailAlloc_4095_;
goto v_reusejp_4093_;
}
v_reusejp_4093_:
{
return v___x_4094_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__8(lean_object* v_pre_4097_, lean_object* v_post_4098_, lean_object* v_e_4099_, lean_object* v_a_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_){
_start:
{
lean_object* v___x_4106_; 
lean_inc_ref(v_post_4098_);
lean_inc(v___y_4104_);
lean_inc_ref(v___y_4103_);
lean_inc(v___y_4102_);
lean_inc_ref(v___y_4101_);
lean_inc_ref(v_e_4099_);
v___x_4106_ = lean_apply_6(v_post_4098_, v_e_4099_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_, lean_box(0));
if (lean_obj_tag(v___x_4106_) == 0)
{
lean_object* v_a_4107_; lean_object* v___x_4109_; uint8_t v_isShared_4110_; uint8_t v_isSharedCheck_4125_; 
v_a_4107_ = lean_ctor_get(v___x_4106_, 0);
v_isSharedCheck_4125_ = !lean_is_exclusive(v___x_4106_);
if (v_isSharedCheck_4125_ == 0)
{
v___x_4109_ = v___x_4106_;
v_isShared_4110_ = v_isSharedCheck_4125_;
goto v_resetjp_4108_;
}
else
{
lean_inc(v_a_4107_);
lean_dec(v___x_4106_);
v___x_4109_ = lean_box(0);
v_isShared_4110_ = v_isSharedCheck_4125_;
goto v_resetjp_4108_;
}
v_resetjp_4108_:
{
switch(lean_obj_tag(v_a_4107_))
{
case 0:
{
lean_object* v_e_4111_; lean_object* v___x_4113_; 
lean_dec(v___y_4104_);
lean_dec_ref(v___y_4103_);
lean_dec(v___y_4102_);
lean_dec_ref(v___y_4101_);
lean_dec(v_a_4100_);
lean_dec_ref(v_e_4099_);
lean_dec_ref(v_post_4098_);
lean_dec_ref(v_pre_4097_);
v_e_4111_ = lean_ctor_get(v_a_4107_, 0);
lean_inc_ref(v_e_4111_);
lean_dec_ref(v_a_4107_);
if (v_isShared_4110_ == 0)
{
lean_ctor_set(v___x_4109_, 0, v_e_4111_);
v___x_4113_ = v___x_4109_;
goto v_reusejp_4112_;
}
else
{
lean_object* v_reuseFailAlloc_4114_; 
v_reuseFailAlloc_4114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4114_, 0, v_e_4111_);
v___x_4113_ = v_reuseFailAlloc_4114_;
goto v_reusejp_4112_;
}
v_reusejp_4112_:
{
return v___x_4113_;
}
}
case 1:
{
lean_object* v_e_4115_; lean_object* v___x_4116_; 
lean_del_object(v___x_4109_);
lean_dec_ref(v_e_4099_);
v_e_4115_ = lean_ctor_get(v_a_4107_, 0);
lean_inc_ref(v_e_4115_);
lean_dec_ref(v_a_4107_);
v___x_4116_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_4097_, v_post_4098_, v_e_4115_, v_a_4100_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_);
return v___x_4116_;
}
default: 
{
lean_object* v_e_x3f_4117_; 
lean_dec(v___y_4104_);
lean_dec_ref(v___y_4103_);
lean_dec(v___y_4102_);
lean_dec_ref(v___y_4101_);
lean_dec(v_a_4100_);
lean_dec_ref(v_post_4098_);
lean_dec_ref(v_pre_4097_);
v_e_x3f_4117_ = lean_ctor_get(v_a_4107_, 0);
lean_inc(v_e_x3f_4117_);
lean_dec_ref(v_a_4107_);
if (lean_obj_tag(v_e_x3f_4117_) == 0)
{
lean_object* v___x_4119_; 
if (v_isShared_4110_ == 0)
{
lean_ctor_set(v___x_4109_, 0, v_e_4099_);
v___x_4119_ = v___x_4109_;
goto v_reusejp_4118_;
}
else
{
lean_object* v_reuseFailAlloc_4120_; 
v_reuseFailAlloc_4120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4120_, 0, v_e_4099_);
v___x_4119_ = v_reuseFailAlloc_4120_;
goto v_reusejp_4118_;
}
v_reusejp_4118_:
{
return v___x_4119_;
}
}
else
{
lean_object* v_val_4121_; lean_object* v___x_4123_; 
lean_dec_ref(v_e_4099_);
v_val_4121_ = lean_ctor_get(v_e_x3f_4117_, 0);
lean_inc(v_val_4121_);
lean_dec_ref(v_e_x3f_4117_);
if (v_isShared_4110_ == 0)
{
lean_ctor_set(v___x_4109_, 0, v_val_4121_);
v___x_4123_ = v___x_4109_;
goto v_reusejp_4122_;
}
else
{
lean_object* v_reuseFailAlloc_4124_; 
v_reuseFailAlloc_4124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4124_, 0, v_val_4121_);
v___x_4123_ = v_reuseFailAlloc_4124_;
goto v_reusejp_4122_;
}
v_reusejp_4122_:
{
return v___x_4123_;
}
}
}
}
}
}
else
{
lean_object* v_a_4126_; lean_object* v___x_4128_; uint8_t v_isShared_4129_; uint8_t v_isSharedCheck_4133_; 
lean_dec(v___y_4104_);
lean_dec_ref(v___y_4103_);
lean_dec(v___y_4102_);
lean_dec_ref(v___y_4101_);
lean_dec(v_a_4100_);
lean_dec_ref(v_e_4099_);
lean_dec_ref(v_post_4098_);
lean_dec_ref(v_pre_4097_);
v_a_4126_ = lean_ctor_get(v___x_4106_, 0);
v_isSharedCheck_4133_ = !lean_is_exclusive(v___x_4106_);
if (v_isSharedCheck_4133_ == 0)
{
v___x_4128_ = v___x_4106_;
v_isShared_4129_ = v_isSharedCheck_4133_;
goto v_resetjp_4127_;
}
else
{
lean_inc(v_a_4126_);
lean_dec(v___x_4106_);
v___x_4128_ = lean_box(0);
v_isShared_4129_ = v_isSharedCheck_4133_;
goto v_resetjp_4127_;
}
v_resetjp_4127_:
{
lean_object* v___x_4131_; 
if (v_isShared_4129_ == 0)
{
v___x_4131_ = v___x_4128_;
goto v_reusejp_4130_;
}
else
{
lean_object* v_reuseFailAlloc_4132_; 
v_reuseFailAlloc_4132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4132_, 0, v_a_4126_);
v___x_4131_ = v_reuseFailAlloc_4132_;
goto v_reusejp_4130_;
}
v_reusejp_4130_:
{
return v___x_4131_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__8___boxed(lean_object* v_pre_4134_, lean_object* v_post_4135_, lean_object* v_e_4136_, lean_object* v_a_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_){
_start:
{
lean_object* v_res_4143_; 
v_res_4143_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__8(v_pre_4134_, v_post_4135_, v_e_4136_, v_a_4137_, v___y_4138_, v___y_4139_, v___y_4140_, v___y_4141_);
return v_res_4143_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7___boxed(lean_object* v_pre_4144_, lean_object* v_post_4145_, lean_object* v_sz_4146_, lean_object* v_i_4147_, lean_object* v_bs_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_){
_start:
{
size_t v_sz_boxed_4155_; size_t v_i_boxed_4156_; lean_object* v_res_4157_; 
v_sz_boxed_4155_ = lean_unbox_usize(v_sz_4146_);
lean_dec(v_sz_4146_);
v_i_boxed_4156_ = lean_unbox_usize(v_i_4147_);
lean_dec(v_i_4147_);
v_res_4157_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_4144_, v_post_4145_, v_sz_boxed_4155_, v_i_boxed_4156_, v_bs_4148_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_);
return v_res_4157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9___boxed(lean_object* v_pre_4158_, lean_object* v_post_4159_, lean_object* v_x_4160_, lean_object* v_x_4161_, lean_object* v_x_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_){
_start:
{
lean_object* v_res_4169_; 
v_res_4169_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9(v_pre_4158_, v_post_4159_, v_x_4160_, v_x_4161_, v_x_4162_, v___y_4163_, v___y_4164_, v___y_4165_, v___y_4166_, v___y_4167_);
return v_res_4169_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4___boxed(lean_object* v_pre_4170_, lean_object* v_post_4171_, lean_object* v_e_4172_, lean_object* v_a_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_){
_start:
{
lean_object* v_res_4179_; 
v_res_4179_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_4170_, v_post_4171_, v_e_4172_, v_a_4173_, v___y_4174_, v___y_4175_, v___y_4176_, v___y_4177_);
return v_res_4179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4(lean_object* v_input_4180_, lean_object* v_pre_4181_, lean_object* v_post_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_){
_start:
{
lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v_a_4190_; lean_object* v___x_4191_; 
v___x_4188_ = lean_obj_once(&l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__2, &l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__2_once, _init_l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__2);
v___x_4189_ = l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___lam__0(lean_box(0), v___x_4188_, v___y_4183_, v___y_4184_, v___y_4185_, v___y_4186_);
v_a_4190_ = lean_ctor_get(v___x_4189_, 0);
lean_inc(v_a_4190_);
lean_dec_ref(v___x_4189_);
lean_inc(v___y_4186_);
lean_inc_ref(v___y_4185_);
lean_inc(v___y_4184_);
lean_inc_ref(v___y_4183_);
lean_inc(v_a_4190_);
v___x_4191_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_4181_, v_post_4182_, v_input_4180_, v_a_4190_, v___y_4183_, v___y_4184_, v___y_4185_, v___y_4186_);
if (lean_obj_tag(v___x_4191_) == 0)
{
lean_object* v_a_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4196_; uint8_t v_isShared_4197_; uint8_t v_isSharedCheck_4201_; 
v_a_4192_ = lean_ctor_get(v___x_4191_, 0);
lean_inc(v_a_4192_);
lean_dec_ref(v___x_4191_);
v___x_4193_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_4193_, 0, lean_box(0));
lean_closure_set(v___x_4193_, 1, lean_box(0));
lean_closure_set(v___x_4193_, 2, v_a_4190_);
v___x_4194_ = l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___lam__0(lean_box(0), v___x_4193_, v___y_4183_, v___y_4184_, v___y_4185_, v___y_4186_);
lean_dec(v___y_4186_);
lean_dec_ref(v___y_4185_);
lean_dec(v___y_4184_);
lean_dec_ref(v___y_4183_);
v_isSharedCheck_4201_ = !lean_is_exclusive(v___x_4194_);
if (v_isSharedCheck_4201_ == 0)
{
lean_object* v_unused_4202_; 
v_unused_4202_ = lean_ctor_get(v___x_4194_, 0);
lean_dec(v_unused_4202_);
v___x_4196_ = v___x_4194_;
v_isShared_4197_ = v_isSharedCheck_4201_;
goto v_resetjp_4195_;
}
else
{
lean_dec(v___x_4194_);
v___x_4196_ = lean_box(0);
v_isShared_4197_ = v_isSharedCheck_4201_;
goto v_resetjp_4195_;
}
v_resetjp_4195_:
{
lean_object* v___x_4199_; 
if (v_isShared_4197_ == 0)
{
lean_ctor_set(v___x_4196_, 0, v_a_4192_);
v___x_4199_ = v___x_4196_;
goto v_reusejp_4198_;
}
else
{
lean_object* v_reuseFailAlloc_4200_; 
v_reuseFailAlloc_4200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4200_, 0, v_a_4192_);
v___x_4199_ = v_reuseFailAlloc_4200_;
goto v_reusejp_4198_;
}
v_reusejp_4198_:
{
return v___x_4199_;
}
}
}
else
{
lean_dec(v_a_4190_);
lean_dec(v___y_4186_);
lean_dec_ref(v___y_4185_);
lean_dec(v___y_4184_);
lean_dec_ref(v___y_4183_);
return v___x_4191_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4___boxed(lean_object* v_input_4203_, lean_object* v_pre_4204_, lean_object* v_post_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_){
_start:
{
lean_object* v_res_4211_; 
v_res_4211_ = l_Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4(v_input_4203_, v_pre_4204_, v_post_4205_, v___y_4206_, v___y_4207_, v___y_4208_, v___y_4209_);
return v_res_4211_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__6___closed__0(void){
_start:
{
lean_object* v___x_4212_; double v___x_4213_; 
v___x_4212_ = lean_unsigned_to_nat(0u);
v___x_4213_ = lean_float_of_nat(v___x_4212_);
return v___x_4213_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__6(lean_object* v_cls_4217_, lean_object* v_msg_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_){
_start:
{
lean_object* v_ref_4224_; lean_object* v___x_4225_; lean_object* v_a_4226_; lean_object* v___x_4228_; uint8_t v_isShared_4229_; uint8_t v_isSharedCheck_4270_; 
v_ref_4224_ = lean_ctor_get(v___y_4221_, 5);
v___x_4225_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15_spec__16(v_msg_4218_, v___y_4219_, v___y_4220_, v___y_4221_, v___y_4222_);
v_a_4226_ = lean_ctor_get(v___x_4225_, 0);
v_isSharedCheck_4270_ = !lean_is_exclusive(v___x_4225_);
if (v_isSharedCheck_4270_ == 0)
{
v___x_4228_ = v___x_4225_;
v_isShared_4229_ = v_isSharedCheck_4270_;
goto v_resetjp_4227_;
}
else
{
lean_inc(v_a_4226_);
lean_dec(v___x_4225_);
v___x_4228_ = lean_box(0);
v_isShared_4229_ = v_isSharedCheck_4270_;
goto v_resetjp_4227_;
}
v_resetjp_4227_:
{
lean_object* v___x_4230_; lean_object* v_traceState_4231_; lean_object* v_env_4232_; lean_object* v_nextMacroScope_4233_; lean_object* v_ngen_4234_; lean_object* v_auxDeclNGen_4235_; lean_object* v_cache_4236_; lean_object* v_messages_4237_; lean_object* v_infoState_4238_; lean_object* v_snapshotTasks_4239_; lean_object* v___x_4241_; uint8_t v_isShared_4242_; uint8_t v_isSharedCheck_4269_; 
v___x_4230_ = lean_st_ref_take(v___y_4222_);
v_traceState_4231_ = lean_ctor_get(v___x_4230_, 4);
v_env_4232_ = lean_ctor_get(v___x_4230_, 0);
v_nextMacroScope_4233_ = lean_ctor_get(v___x_4230_, 1);
v_ngen_4234_ = lean_ctor_get(v___x_4230_, 2);
v_auxDeclNGen_4235_ = lean_ctor_get(v___x_4230_, 3);
v_cache_4236_ = lean_ctor_get(v___x_4230_, 5);
v_messages_4237_ = lean_ctor_get(v___x_4230_, 6);
v_infoState_4238_ = lean_ctor_get(v___x_4230_, 7);
v_snapshotTasks_4239_ = lean_ctor_get(v___x_4230_, 8);
v_isSharedCheck_4269_ = !lean_is_exclusive(v___x_4230_);
if (v_isSharedCheck_4269_ == 0)
{
v___x_4241_ = v___x_4230_;
v_isShared_4242_ = v_isSharedCheck_4269_;
goto v_resetjp_4240_;
}
else
{
lean_inc(v_snapshotTasks_4239_);
lean_inc(v_infoState_4238_);
lean_inc(v_messages_4237_);
lean_inc(v_cache_4236_);
lean_inc(v_traceState_4231_);
lean_inc(v_auxDeclNGen_4235_);
lean_inc(v_ngen_4234_);
lean_inc(v_nextMacroScope_4233_);
lean_inc(v_env_4232_);
lean_dec(v___x_4230_);
v___x_4241_ = lean_box(0);
v_isShared_4242_ = v_isSharedCheck_4269_;
goto v_resetjp_4240_;
}
v_resetjp_4240_:
{
uint64_t v_tid_4243_; lean_object* v_traces_4244_; lean_object* v___x_4246_; uint8_t v_isShared_4247_; uint8_t v_isSharedCheck_4268_; 
v_tid_4243_ = lean_ctor_get_uint64(v_traceState_4231_, sizeof(void*)*1);
v_traces_4244_ = lean_ctor_get(v_traceState_4231_, 0);
v_isSharedCheck_4268_ = !lean_is_exclusive(v_traceState_4231_);
if (v_isSharedCheck_4268_ == 0)
{
v___x_4246_ = v_traceState_4231_;
v_isShared_4247_ = v_isSharedCheck_4268_;
goto v_resetjp_4245_;
}
else
{
lean_inc(v_traces_4244_);
lean_dec(v_traceState_4231_);
v___x_4246_ = lean_box(0);
v_isShared_4247_ = v_isSharedCheck_4268_;
goto v_resetjp_4245_;
}
v_resetjp_4245_:
{
lean_object* v___x_4248_; double v___x_4249_; uint8_t v___x_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4258_; 
v___x_4248_ = lean_box(0);
v___x_4249_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__6___closed__0, &l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__6___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__6___closed__0);
v___x_4250_ = 0;
v___x_4251_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__6___closed__1));
v___x_4252_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4252_, 0, v_cls_4217_);
lean_ctor_set(v___x_4252_, 1, v___x_4248_);
lean_ctor_set(v___x_4252_, 2, v___x_4251_);
lean_ctor_set_float(v___x_4252_, sizeof(void*)*3, v___x_4249_);
lean_ctor_set_float(v___x_4252_, sizeof(void*)*3 + 8, v___x_4249_);
lean_ctor_set_uint8(v___x_4252_, sizeof(void*)*3 + 16, v___x_4250_);
v___x_4253_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__6___closed__2));
v___x_4254_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4254_, 0, v___x_4252_);
lean_ctor_set(v___x_4254_, 1, v_a_4226_);
lean_ctor_set(v___x_4254_, 2, v___x_4253_);
lean_inc(v_ref_4224_);
v___x_4255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4255_, 0, v_ref_4224_);
lean_ctor_set(v___x_4255_, 1, v___x_4254_);
v___x_4256_ = l_Lean_PersistentArray_push___redArg(v_traces_4244_, v___x_4255_);
if (v_isShared_4247_ == 0)
{
lean_ctor_set(v___x_4246_, 0, v___x_4256_);
v___x_4258_ = v___x_4246_;
goto v_reusejp_4257_;
}
else
{
lean_object* v_reuseFailAlloc_4267_; 
v_reuseFailAlloc_4267_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4267_, 0, v___x_4256_);
lean_ctor_set_uint64(v_reuseFailAlloc_4267_, sizeof(void*)*1, v_tid_4243_);
v___x_4258_ = v_reuseFailAlloc_4267_;
goto v_reusejp_4257_;
}
v_reusejp_4257_:
{
lean_object* v___x_4260_; 
if (v_isShared_4242_ == 0)
{
lean_ctor_set(v___x_4241_, 4, v___x_4258_);
v___x_4260_ = v___x_4241_;
goto v_reusejp_4259_;
}
else
{
lean_object* v_reuseFailAlloc_4266_; 
v_reuseFailAlloc_4266_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4266_, 0, v_env_4232_);
lean_ctor_set(v_reuseFailAlloc_4266_, 1, v_nextMacroScope_4233_);
lean_ctor_set(v_reuseFailAlloc_4266_, 2, v_ngen_4234_);
lean_ctor_set(v_reuseFailAlloc_4266_, 3, v_auxDeclNGen_4235_);
lean_ctor_set(v_reuseFailAlloc_4266_, 4, v___x_4258_);
lean_ctor_set(v_reuseFailAlloc_4266_, 5, v_cache_4236_);
lean_ctor_set(v_reuseFailAlloc_4266_, 6, v_messages_4237_);
lean_ctor_set(v_reuseFailAlloc_4266_, 7, v_infoState_4238_);
lean_ctor_set(v_reuseFailAlloc_4266_, 8, v_snapshotTasks_4239_);
v___x_4260_ = v_reuseFailAlloc_4266_;
goto v_reusejp_4259_;
}
v_reusejp_4259_:
{
lean_object* v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4264_; 
v___x_4261_ = lean_st_ref_set(v___y_4222_, v___x_4260_);
v___x_4262_ = lean_box(0);
if (v_isShared_4229_ == 0)
{
lean_ctor_set(v___x_4228_, 0, v___x_4262_);
v___x_4264_ = v___x_4228_;
goto v_reusejp_4263_;
}
else
{
lean_object* v_reuseFailAlloc_4265_; 
v_reuseFailAlloc_4265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4265_, 0, v___x_4262_);
v___x_4264_ = v_reuseFailAlloc_4265_;
goto v_reusejp_4263_;
}
v_reusejp_4263_:
{
return v___x_4264_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__6___boxed(lean_object* v_cls_4271_, lean_object* v_msg_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_, lean_object* v___y_4277_){
_start:
{
lean_object* v_res_4278_; 
v_res_4278_ = l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__6(v_cls_4271_, v_msg_4272_, v___y_4273_, v___y_4274_, v___y_4275_, v___y_4276_);
lean_dec(v___y_4276_);
lean_dec_ref(v___y_4275_);
lean_dec(v___y_4274_);
lean_dec_ref(v___y_4273_);
return v_res_4278_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_preprocess_spec__2(size_t v_sz_4279_, size_t v_i_4280_, lean_object* v_bs_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_){
_start:
{
uint8_t v___x_4287_; 
v___x_4287_ = lean_usize_dec_lt(v_i_4280_, v_sz_4279_);
if (v___x_4287_ == 0)
{
lean_object* v___x_4288_; 
lean_dec(v___y_4285_);
lean_dec_ref(v___y_4284_);
lean_dec(v___y_4283_);
lean_dec_ref(v___y_4282_);
v___x_4288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4288_, 0, v_bs_4281_);
return v___x_4288_;
}
else
{
lean_object* v_v_4289_; lean_object* v___x_4290_; 
v_v_4289_ = lean_array_uget_borrowed(v_bs_4281_, v_i_4280_);
lean_inc(v___y_4285_);
lean_inc_ref(v___y_4284_);
lean_inc(v___y_4283_);
lean_inc_ref(v___y_4282_);
lean_inc(v_v_4289_);
v___x_4290_ = l_Lean_Elab_WF_mkWfParam(v_v_4289_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_);
if (lean_obj_tag(v___x_4290_) == 0)
{
lean_object* v_a_4291_; lean_object* v___x_4292_; lean_object* v_bs_x27_4293_; size_t v___x_4294_; size_t v___x_4295_; lean_object* v___x_4296_; 
v_a_4291_ = lean_ctor_get(v___x_4290_, 0);
lean_inc(v_a_4291_);
lean_dec_ref(v___x_4290_);
v___x_4292_ = lean_unsigned_to_nat(0u);
v_bs_x27_4293_ = lean_array_uset(v_bs_4281_, v_i_4280_, v___x_4292_);
v___x_4294_ = ((size_t)1ULL);
v___x_4295_ = lean_usize_add(v_i_4280_, v___x_4294_);
v___x_4296_ = lean_array_uset(v_bs_x27_4293_, v_i_4280_, v_a_4291_);
v_i_4280_ = v___x_4295_;
v_bs_4281_ = v___x_4296_;
goto _start;
}
else
{
lean_object* v_a_4298_; lean_object* v___x_4300_; uint8_t v_isShared_4301_; uint8_t v_isSharedCheck_4305_; 
lean_dec(v___y_4285_);
lean_dec_ref(v___y_4284_);
lean_dec(v___y_4283_);
lean_dec_ref(v___y_4282_);
lean_dec_ref(v_bs_4281_);
v_a_4298_ = lean_ctor_get(v___x_4290_, 0);
v_isSharedCheck_4305_ = !lean_is_exclusive(v___x_4290_);
if (v_isSharedCheck_4305_ == 0)
{
v___x_4300_ = v___x_4290_;
v_isShared_4301_ = v_isSharedCheck_4305_;
goto v_resetjp_4299_;
}
else
{
lean_inc(v_a_4298_);
lean_dec(v___x_4290_);
v___x_4300_ = lean_box(0);
v_isShared_4301_ = v_isSharedCheck_4305_;
goto v_resetjp_4299_;
}
v_resetjp_4299_:
{
lean_object* v___x_4303_; 
if (v_isShared_4301_ == 0)
{
v___x_4303_ = v___x_4300_;
goto v_reusejp_4302_;
}
else
{
lean_object* v_reuseFailAlloc_4304_; 
v_reuseFailAlloc_4304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4304_, 0, v_a_4298_);
v___x_4303_ = v_reuseFailAlloc_4304_;
goto v_reusejp_4302_;
}
v_reusejp_4302_:
{
return v___x_4303_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_preprocess_spec__2___boxed(lean_object* v_sz_4306_, lean_object* v_i_4307_, lean_object* v_bs_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_, lean_object* v___y_4312_, lean_object* v___y_4313_){
_start:
{
size_t v_sz_boxed_4314_; size_t v_i_boxed_4315_; lean_object* v_res_4316_; 
v_sz_boxed_4314_ = lean_unbox_usize(v_sz_4306_);
lean_dec(v_sz_4306_);
v_i_boxed_4315_ = lean_unbox_usize(v_i_4307_);
lean_dec(v_i_4307_);
v_res_4316_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_preprocess_spec__2(v_sz_boxed_4314_, v_i_boxed_4315_, v_bs_4308_, v___y_4309_, v___y_4310_, v___y_4311_, v___y_4312_);
return v_res_4316_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__0___closed__0(void){
_start:
{
lean_object* v___x_4317_; 
v___x_4317_ = l_Lean_Meta_DiscrTree_empty(lean_box(0));
return v___x_4317_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4318_; 
v___x_4318_ = l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3(lean_box(0));
return v___x_4318_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; 
v___x_4319_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__0___closed__1, &l_Lean_Elab_WF_preprocess___lam__0___closed__1_once, _init_l_Lean_Elab_WF_preprocess___lam__0___closed__1);
v___x_4320_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__0___closed__0, &l_Lean_Elab_WF_preprocess___lam__0___closed__0_once, _init_l_Lean_Elab_WF_preprocess___lam__0___closed__0);
v___x_4321_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4321_, 0, v___x_4320_);
lean_ctor_set(v___x_4321_, 1, v___x_4320_);
lean_ctor_set(v___x_4321_, 2, v___x_4319_);
lean_ctor_set(v___x_4321_, 3, v___x_4319_);
return v___x_4321_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4322_; 
v___x_4322_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4322_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__0___closed__4(void){
_start:
{
lean_object* v___x_4323_; lean_object* v___x_4324_; 
v___x_4323_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__0___closed__3, &l_Lean_Elab_WF_preprocess___lam__0___closed__3_once, _init_l_Lean_Elab_WF_preprocess___lam__0___closed__3);
v___x_4324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4324_, 0, v___x_4323_);
return v___x_4324_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; 
v___x_4325_ = lean_unsigned_to_nat(0u);
v___x_4326_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__0___closed__4, &l_Lean_Elab_WF_preprocess___lam__0___closed__4_once, _init_l_Lean_Elab_WF_preprocess___lam__0___closed__4);
v___x_4327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4327_, 0, v___x_4326_);
lean_ctor_set(v___x_4327_, 1, v___x_4325_);
return v___x_4327_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__0___closed__6(void){
_start:
{
lean_object* v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; 
v___x_4328_ = lean_unsigned_to_nat(32u);
v___x_4329_ = lean_mk_empty_array_with_capacity(v___x_4328_);
v___x_4330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4330_, 0, v___x_4329_);
return v___x_4330_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__0___closed__7(void){
_start:
{
size_t v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; 
v___x_4331_ = ((size_t)5ULL);
v___x_4332_ = lean_unsigned_to_nat(0u);
v___x_4333_ = lean_unsigned_to_nat(32u);
v___x_4334_ = lean_mk_empty_array_with_capacity(v___x_4333_);
v___x_4335_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__0___closed__6, &l_Lean_Elab_WF_preprocess___lam__0___closed__6_once, _init_l_Lean_Elab_WF_preprocess___lam__0___closed__6);
v___x_4336_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4336_, 0, v___x_4335_);
lean_ctor_set(v___x_4336_, 1, v___x_4334_);
lean_ctor_set(v___x_4336_, 2, v___x_4332_);
lean_ctor_set(v___x_4336_, 3, v___x_4332_);
lean_ctor_set_usize(v___x_4336_, 4, v___x_4331_);
return v___x_4336_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__0___closed__8(void){
_start:
{
lean_object* v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; 
v___x_4337_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__0___closed__7, &l_Lean_Elab_WF_preprocess___lam__0___closed__7_once, _init_l_Lean_Elab_WF_preprocess___lam__0___closed__7);
v___x_4338_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__0___closed__4, &l_Lean_Elab_WF_preprocess___lam__0___closed__4_once, _init_l_Lean_Elab_WF_preprocess___lam__0___closed__4);
v___x_4339_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4339_, 0, v___x_4338_);
lean_ctor_set(v___x_4339_, 1, v___x_4338_);
lean_ctor_set(v___x_4339_, 2, v___x_4338_);
lean_ctor_set(v___x_4339_, 3, v___x_4337_);
return v___x_4339_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__0___closed__9(void){
_start:
{
lean_object* v___x_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; 
v___x_4340_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__0___closed__8, &l_Lean_Elab_WF_preprocess___lam__0___closed__8_once, _init_l_Lean_Elab_WF_preprocess___lam__0___closed__8);
v___x_4341_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__0___closed__5, &l_Lean_Elab_WF_preprocess___lam__0___closed__5_once, _init_l_Lean_Elab_WF_preprocess___lam__0___closed__5);
v___x_4342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4342_, 0, v___x_4341_);
lean_ctor_set(v___x_4342_, 1, v___x_4340_);
return v___x_4342_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__0___closed__13(void){
_start:
{
lean_object* v___x_4349_; lean_object* v___x_4350_; 
v___x_4349_ = ((lean_object*)(l_Lean_Elab_WF_preprocess___lam__0___closed__12));
v___x_4350_ = l_Lean_stringToMessageData(v___x_4349_);
return v___x_4350_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__0___closed__15(void){
_start:
{
lean_object* v___x_4352_; lean_object* v___x_4353_; 
v___x_4352_ = ((lean_object*)(l_Lean_Elab_WF_preprocess___lam__0___closed__14));
v___x_4353_ = l_Lean_stringToMessageData(v___x_4352_);
return v___x_4353_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__0___closed__17(void){
_start:
{
lean_object* v___x_4355_; lean_object* v___x_4356_; 
v___x_4355_ = ((lean_object*)(l_Lean_Elab_WF_preprocess___lam__0___closed__16));
v___x_4356_ = l_Lean_stringToMessageData(v___x_4355_);
return v___x_4356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preprocess___lam__0(uint8_t v___x_4357_, lean_object* v_a_4358_, lean_object* v___f_4359_, lean_object* v___f_4360_, lean_object* v_xs_4361_, lean_object* v_x_4362_, lean_object* v___y_4363_, lean_object* v___y_4364_, lean_object* v___y_4365_, lean_object* v___y_4366_){
_start:
{
size_t v_sz_4368_; size_t v___x_4369_; lean_object* v___x_4370_; 
v_sz_4368_ = lean_array_size(v_xs_4361_);
v___x_4369_ = ((size_t)0ULL);
lean_inc(v___y_4366_);
lean_inc_ref(v___y_4365_);
lean_inc(v___y_4364_);
lean_inc_ref(v___y_4363_);
lean_inc_ref(v_xs_4361_);
v___x_4370_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_preprocess_spec__2(v_sz_4368_, v___x_4369_, v_xs_4361_, v___y_4363_, v___y_4364_, v___y_4365_, v___y_4366_);
if (lean_obj_tag(v___x_4370_) == 0)
{
lean_object* v_a_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; 
v_a_4371_ = lean_ctor_get(v___x_4370_, 0);
lean_inc(v_a_4371_);
lean_dec_ref(v___x_4370_);
v___x_4372_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__0___closed__2, &l_Lean_Elab_WF_preprocess___lam__0___closed__2_once, _init_l_Lean_Elab_WF_preprocess___lam__0___closed__2);
v___x_4373_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__26___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_12_));
v___x_4374_ = l_Lean_Meta_Simp_Simprocs_add(v___x_4372_, v___x_4373_, v___x_4357_, v___y_4365_, v___y_4366_);
if (lean_obj_tag(v___x_4374_) == 0)
{
lean_object* v_a_4375_; lean_object* v___x_4376_; uint8_t v___x_4377_; lean_object* v___x_4378_; 
v_a_4375_ = lean_ctor_get(v___x_4374_, 0);
lean_inc(v_a_4375_);
lean_dec_ref(v___x_4374_);
v___x_4376_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__31___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_12_));
v___x_4377_ = 0;
v___x_4378_ = l_Lean_Meta_Simp_Simprocs_add(v_a_4375_, v___x_4376_, v___x_4377_, v___y_4365_, v___y_4366_);
if (lean_obj_tag(v___x_4378_) == 0)
{
lean_object* v_a_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; 
v_a_4379_ = lean_ctor_get(v___x_4378_, 0);
lean_inc(v_a_4379_);
lean_dec_ref(v___x_4378_);
v___x_4380_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__52___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12_));
v___x_4381_ = l_Lean_Meta_Simp_Simprocs_add(v_a_4379_, v___x_4380_, v___x_4357_, v___y_4365_, v___y_4366_);
if (lean_obj_tag(v___x_4381_) == 0)
{
lean_object* v_a_4382_; lean_object* v___x_4383_; 
v_a_4382_ = lean_ctor_get(v___x_4381_, 0);
lean_inc(v_a_4382_);
lean_dec_ref(v___x_4381_);
v___x_4383_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg(v___y_4363_, v___y_4365_, v___y_4366_);
if (lean_obj_tag(v___x_4383_) == 0)
{
lean_object* v_a_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; 
v_a_4384_ = lean_ctor_get(v___x_4383_, 0);
lean_inc(v_a_4384_);
lean_dec_ref(v___x_4383_);
v___x_4385_ = l_Lean_Expr_beta(v_a_4358_, v_a_4371_);
v___x_4386_ = lean_unsigned_to_nat(1u);
v___x_4387_ = lean_mk_empty_array_with_capacity(v___x_4386_);
v___x_4388_ = lean_array_push(v___x_4387_, v_a_4382_);
v___x_4389_ = lean_box(0);
v___x_4390_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__0___closed__9, &l_Lean_Elab_WF_preprocess___lam__0___closed__9_once, _init_l_Lean_Elab_WF_preprocess___lam__0___closed__9);
lean_inc(v___y_4366_);
lean_inc_ref(v___y_4365_);
lean_inc(v___y_4364_);
lean_inc_ref(v___y_4363_);
lean_inc_ref(v___x_4385_);
v___x_4391_ = l_Lean_Meta_simp(v___x_4385_, v_a_4384_, v___x_4388_, v___x_4389_, v___x_4390_, v___y_4363_, v___y_4364_, v___y_4365_, v___y_4366_);
if (lean_obj_tag(v___x_4391_) == 0)
{
lean_object* v_a_4392_; lean_object* v_fst_4393_; lean_object* v___x_4395_; uint8_t v_isShared_4396_; uint8_t v_isSharedCheck_4459_; 
v_a_4392_ = lean_ctor_get(v___x_4391_, 0);
lean_inc(v_a_4392_);
lean_dec_ref(v___x_4391_);
v_fst_4393_ = lean_ctor_get(v_a_4392_, 0);
v_isSharedCheck_4459_ = !lean_is_exclusive(v_a_4392_);
if (v_isSharedCheck_4459_ == 0)
{
lean_object* v_unused_4460_; 
v_unused_4460_ = lean_ctor_get(v_a_4392_, 1);
lean_dec(v_unused_4460_);
v___x_4395_ = v_a_4392_;
v_isShared_4396_ = v_isSharedCheck_4459_;
goto v_resetjp_4394_;
}
else
{
lean_inc(v_fst_4393_);
lean_dec(v_a_4392_);
v___x_4395_ = lean_box(0);
v_isShared_4396_ = v_isSharedCheck_4459_;
goto v_resetjp_4394_;
}
v_resetjp_4394_:
{
lean_object* v_expr_4397_; lean_object* v_proof_x3f_4398_; uint8_t v_cache_4399_; lean_object* v___x_4401_; uint8_t v_isShared_4402_; uint8_t v_isSharedCheck_4458_; 
v_expr_4397_ = lean_ctor_get(v_fst_4393_, 0);
v_proof_x3f_4398_ = lean_ctor_get(v_fst_4393_, 1);
v_cache_4399_ = lean_ctor_get_uint8(v_fst_4393_, sizeof(void*)*2);
v_isSharedCheck_4458_ = !lean_is_exclusive(v_fst_4393_);
if (v_isSharedCheck_4458_ == 0)
{
v___x_4401_ = v_fst_4393_;
v_isShared_4402_ = v_isSharedCheck_4458_;
goto v_resetjp_4400_;
}
else
{
lean_inc(v_proof_x3f_4398_);
lean_inc(v_expr_4397_);
lean_dec(v_fst_4393_);
v___x_4401_ = lean_box(0);
v_isShared_4402_ = v_isSharedCheck_4458_;
goto v_resetjp_4400_;
}
v_resetjp_4400_:
{
lean_object* v___x_4403_; 
lean_inc(v___y_4366_);
lean_inc_ref(v___y_4365_);
lean_inc(v___y_4364_);
lean_inc_ref(v___y_4363_);
lean_inc_ref(v_expr_4397_);
v___x_4403_ = l_Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4(v_expr_4397_, v___f_4359_, v___f_4360_, v___y_4363_, v___y_4364_, v___y_4365_, v___y_4366_);
if (lean_obj_tag(v___x_4403_) == 0)
{
lean_object* v_a_4404_; lean_object* v___x_4405_; 
v_a_4404_ = lean_ctor_get(v___x_4403_, 0);
lean_inc(v_a_4404_);
lean_dec_ref(v___x_4403_);
lean_inc(v___y_4366_);
lean_inc_ref(v___y_4365_);
lean_inc(v___y_4364_);
lean_inc_ref(v___y_4363_);
v___x_4405_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet(v_a_4404_, v___y_4363_, v___y_4364_, v___y_4365_, v___y_4366_);
if (lean_obj_tag(v___x_4405_) == 0)
{
lean_object* v_a_4406_; lean_object* v___y_4408_; lean_object* v___y_4409_; lean_object* v___y_4410_; lean_object* v___y_4411_; lean_object* v___x_4416_; lean_object* v___x_4417_; lean_object* v_a_4418_; uint8_t v___x_4419_; 
v_a_4406_ = lean_ctor_get(v___x_4405_, 0);
lean_inc(v_a_4406_);
lean_dec_ref(v___x_4405_);
v___x_4416_ = ((lean_object*)(l_Lean_Elab_WF_preprocess___lam__0___closed__11));
v___x_4417_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_WF_preprocess_spec__5___redArg(v___x_4416_, v___y_4365_);
v_a_4418_ = lean_ctor_get(v___x_4417_, 0);
lean_inc(v_a_4418_);
lean_dec_ref(v___x_4417_);
v___x_4419_ = lean_unbox(v_a_4418_);
lean_dec(v_a_4418_);
if (v___x_4419_ == 0)
{
lean_dec_ref(v_expr_4397_);
lean_del_object(v___x_4395_);
lean_dec_ref(v___x_4385_);
v___y_4408_ = v___y_4363_;
v___y_4409_ = v___y_4364_;
v___y_4410_ = v___y_4365_;
v___y_4411_ = v___y_4366_;
goto v___jp_4407_;
}
else
{
lean_object* v___x_4420_; lean_object* v___x_4421_; lean_object* v___x_4423_; 
v___x_4420_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__0___closed__13, &l_Lean_Elab_WF_preprocess___lam__0___closed__13_once, _init_l_Lean_Elab_WF_preprocess___lam__0___closed__13);
v___x_4421_ = l_Lean_indentExpr(v___x_4385_);
if (v_isShared_4396_ == 0)
{
lean_ctor_set_tag(v___x_4395_, 7);
lean_ctor_set(v___x_4395_, 1, v___x_4421_);
lean_ctor_set(v___x_4395_, 0, v___x_4420_);
v___x_4423_ = v___x_4395_;
goto v_reusejp_4422_;
}
else
{
lean_object* v_reuseFailAlloc_4441_; 
v_reuseFailAlloc_4441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4441_, 0, v___x_4420_);
lean_ctor_set(v_reuseFailAlloc_4441_, 1, v___x_4421_);
v___x_4423_ = v_reuseFailAlloc_4441_;
goto v_reusejp_4422_;
}
v_reusejp_4422_:
{
lean_object* v___x_4424_; lean_object* v___x_4425_; lean_object* v___x_4426_; lean_object* v___x_4427_; lean_object* v___x_4428_; lean_object* v___x_4429_; lean_object* v___x_4430_; lean_object* v___x_4431_; lean_object* v___x_4432_; 
v___x_4424_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__0___closed__15, &l_Lean_Elab_WF_preprocess___lam__0___closed__15_once, _init_l_Lean_Elab_WF_preprocess___lam__0___closed__15);
v___x_4425_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4425_, 0, v___x_4423_);
lean_ctor_set(v___x_4425_, 1, v___x_4424_);
v___x_4426_ = l_Lean_indentExpr(v_expr_4397_);
v___x_4427_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4427_, 0, v___x_4425_);
lean_ctor_set(v___x_4427_, 1, v___x_4426_);
v___x_4428_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__0___closed__17, &l_Lean_Elab_WF_preprocess___lam__0___closed__17_once, _init_l_Lean_Elab_WF_preprocess___lam__0___closed__17);
v___x_4429_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4429_, 0, v___x_4427_);
lean_ctor_set(v___x_4429_, 1, v___x_4428_);
lean_inc(v_a_4406_);
v___x_4430_ = l_Lean_indentExpr(v_a_4406_);
v___x_4431_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4431_, 0, v___x_4429_);
lean_ctor_set(v___x_4431_, 1, v___x_4430_);
v___x_4432_ = l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__6(v___x_4416_, v___x_4431_, v___y_4363_, v___y_4364_, v___y_4365_, v___y_4366_);
if (lean_obj_tag(v___x_4432_) == 0)
{
lean_dec_ref(v___x_4432_);
v___y_4408_ = v___y_4363_;
v___y_4409_ = v___y_4364_;
v___y_4410_ = v___y_4365_;
v___y_4411_ = v___y_4366_;
goto v___jp_4407_;
}
else
{
lean_object* v_a_4433_; lean_object* v___x_4435_; uint8_t v_isShared_4436_; uint8_t v_isSharedCheck_4440_; 
lean_dec(v_a_4406_);
lean_del_object(v___x_4401_);
lean_dec(v_proof_x3f_4398_);
lean_dec(v___y_4366_);
lean_dec_ref(v___y_4365_);
lean_dec(v___y_4364_);
lean_dec_ref(v___y_4363_);
lean_dec_ref(v_xs_4361_);
v_a_4433_ = lean_ctor_get(v___x_4432_, 0);
v_isSharedCheck_4440_ = !lean_is_exclusive(v___x_4432_);
if (v_isSharedCheck_4440_ == 0)
{
v___x_4435_ = v___x_4432_;
v_isShared_4436_ = v_isSharedCheck_4440_;
goto v_resetjp_4434_;
}
else
{
lean_inc(v_a_4433_);
lean_dec(v___x_4432_);
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
v___jp_4407_:
{
lean_object* v___x_4413_; 
if (v_isShared_4402_ == 0)
{
lean_ctor_set(v___x_4401_, 0, v_a_4406_);
v___x_4413_ = v___x_4401_;
goto v_reusejp_4412_;
}
else
{
lean_object* v_reuseFailAlloc_4415_; 
v_reuseFailAlloc_4415_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_4415_, 0, v_a_4406_);
lean_ctor_set(v_reuseFailAlloc_4415_, 1, v_proof_x3f_4398_);
lean_ctor_set_uint8(v_reuseFailAlloc_4415_, sizeof(void*)*2, v_cache_4399_);
v___x_4413_ = v_reuseFailAlloc_4415_;
goto v_reusejp_4412_;
}
v_reusejp_4412_:
{
lean_object* v___x_4414_; 
v___x_4414_ = l_Lean_Meta_Simp_Result_addLambdas(v___x_4413_, v_xs_4361_, v___y_4408_, v___y_4409_, v___y_4410_, v___y_4411_);
lean_dec_ref(v_xs_4361_);
return v___x_4414_;
}
}
}
else
{
lean_object* v_a_4442_; lean_object* v___x_4444_; uint8_t v_isShared_4445_; uint8_t v_isSharedCheck_4449_; 
lean_del_object(v___x_4401_);
lean_dec(v_proof_x3f_4398_);
lean_dec_ref(v_expr_4397_);
lean_del_object(v___x_4395_);
lean_dec_ref(v___x_4385_);
lean_dec(v___y_4366_);
lean_dec_ref(v___y_4365_);
lean_dec(v___y_4364_);
lean_dec_ref(v___y_4363_);
lean_dec_ref(v_xs_4361_);
v_a_4442_ = lean_ctor_get(v___x_4405_, 0);
v_isSharedCheck_4449_ = !lean_is_exclusive(v___x_4405_);
if (v_isSharedCheck_4449_ == 0)
{
v___x_4444_ = v___x_4405_;
v_isShared_4445_ = v_isSharedCheck_4449_;
goto v_resetjp_4443_;
}
else
{
lean_inc(v_a_4442_);
lean_dec(v___x_4405_);
v___x_4444_ = lean_box(0);
v_isShared_4445_ = v_isSharedCheck_4449_;
goto v_resetjp_4443_;
}
v_resetjp_4443_:
{
lean_object* v___x_4447_; 
if (v_isShared_4445_ == 0)
{
v___x_4447_ = v___x_4444_;
goto v_reusejp_4446_;
}
else
{
lean_object* v_reuseFailAlloc_4448_; 
v_reuseFailAlloc_4448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4448_, 0, v_a_4442_);
v___x_4447_ = v_reuseFailAlloc_4448_;
goto v_reusejp_4446_;
}
v_reusejp_4446_:
{
return v___x_4447_;
}
}
}
}
else
{
lean_object* v_a_4450_; lean_object* v___x_4452_; uint8_t v_isShared_4453_; uint8_t v_isSharedCheck_4457_; 
lean_del_object(v___x_4401_);
lean_dec(v_proof_x3f_4398_);
lean_dec_ref(v_expr_4397_);
lean_del_object(v___x_4395_);
lean_dec_ref(v___x_4385_);
lean_dec(v___y_4366_);
lean_dec_ref(v___y_4365_);
lean_dec(v___y_4364_);
lean_dec_ref(v___y_4363_);
lean_dec_ref(v_xs_4361_);
v_a_4450_ = lean_ctor_get(v___x_4403_, 0);
v_isSharedCheck_4457_ = !lean_is_exclusive(v___x_4403_);
if (v_isSharedCheck_4457_ == 0)
{
v___x_4452_ = v___x_4403_;
v_isShared_4453_ = v_isSharedCheck_4457_;
goto v_resetjp_4451_;
}
else
{
lean_inc(v_a_4450_);
lean_dec(v___x_4403_);
v___x_4452_ = lean_box(0);
v_isShared_4453_ = v_isSharedCheck_4457_;
goto v_resetjp_4451_;
}
v_resetjp_4451_:
{
lean_object* v___x_4455_; 
if (v_isShared_4453_ == 0)
{
v___x_4455_ = v___x_4452_;
goto v_reusejp_4454_;
}
else
{
lean_object* v_reuseFailAlloc_4456_; 
v_reuseFailAlloc_4456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4456_, 0, v_a_4450_);
v___x_4455_ = v_reuseFailAlloc_4456_;
goto v_reusejp_4454_;
}
v_reusejp_4454_:
{
return v___x_4455_;
}
}
}
}
}
}
else
{
lean_object* v_a_4461_; lean_object* v___x_4463_; uint8_t v_isShared_4464_; uint8_t v_isSharedCheck_4468_; 
lean_dec_ref(v___x_4385_);
lean_dec(v___y_4366_);
lean_dec_ref(v___y_4365_);
lean_dec(v___y_4364_);
lean_dec_ref(v___y_4363_);
lean_dec_ref(v_xs_4361_);
lean_dec_ref(v___f_4360_);
lean_dec_ref(v___f_4359_);
v_a_4461_ = lean_ctor_get(v___x_4391_, 0);
v_isSharedCheck_4468_ = !lean_is_exclusive(v___x_4391_);
if (v_isSharedCheck_4468_ == 0)
{
v___x_4463_ = v___x_4391_;
v_isShared_4464_ = v_isSharedCheck_4468_;
goto v_resetjp_4462_;
}
else
{
lean_inc(v_a_4461_);
lean_dec(v___x_4391_);
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
lean_dec(v_a_4382_);
lean_dec(v_a_4371_);
lean_dec(v___y_4366_);
lean_dec_ref(v___y_4365_);
lean_dec(v___y_4364_);
lean_dec_ref(v___y_4363_);
lean_dec_ref(v_xs_4361_);
lean_dec_ref(v___f_4360_);
lean_dec_ref(v___f_4359_);
lean_dec_ref(v_a_4358_);
v_a_4469_ = lean_ctor_get(v___x_4383_, 0);
v_isSharedCheck_4476_ = !lean_is_exclusive(v___x_4383_);
if (v_isSharedCheck_4476_ == 0)
{
v___x_4471_ = v___x_4383_;
v_isShared_4472_ = v_isSharedCheck_4476_;
goto v_resetjp_4470_;
}
else
{
lean_inc(v_a_4469_);
lean_dec(v___x_4383_);
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
else
{
lean_object* v_a_4477_; lean_object* v___x_4479_; uint8_t v_isShared_4480_; uint8_t v_isSharedCheck_4484_; 
lean_dec(v_a_4371_);
lean_dec(v___y_4366_);
lean_dec_ref(v___y_4365_);
lean_dec(v___y_4364_);
lean_dec_ref(v___y_4363_);
lean_dec_ref(v_xs_4361_);
lean_dec_ref(v___f_4360_);
lean_dec_ref(v___f_4359_);
lean_dec_ref(v_a_4358_);
v_a_4477_ = lean_ctor_get(v___x_4381_, 0);
v_isSharedCheck_4484_ = !lean_is_exclusive(v___x_4381_);
if (v_isSharedCheck_4484_ == 0)
{
v___x_4479_ = v___x_4381_;
v_isShared_4480_ = v_isSharedCheck_4484_;
goto v_resetjp_4478_;
}
else
{
lean_inc(v_a_4477_);
lean_dec(v___x_4381_);
v___x_4479_ = lean_box(0);
v_isShared_4480_ = v_isSharedCheck_4484_;
goto v_resetjp_4478_;
}
v_resetjp_4478_:
{
lean_object* v___x_4482_; 
if (v_isShared_4480_ == 0)
{
v___x_4482_ = v___x_4479_;
goto v_reusejp_4481_;
}
else
{
lean_object* v_reuseFailAlloc_4483_; 
v_reuseFailAlloc_4483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4483_, 0, v_a_4477_);
v___x_4482_ = v_reuseFailAlloc_4483_;
goto v_reusejp_4481_;
}
v_reusejp_4481_:
{
return v___x_4482_;
}
}
}
}
else
{
lean_object* v_a_4485_; lean_object* v___x_4487_; uint8_t v_isShared_4488_; uint8_t v_isSharedCheck_4492_; 
lean_dec(v_a_4371_);
lean_dec(v___y_4366_);
lean_dec_ref(v___y_4365_);
lean_dec(v___y_4364_);
lean_dec_ref(v___y_4363_);
lean_dec_ref(v_xs_4361_);
lean_dec_ref(v___f_4360_);
lean_dec_ref(v___f_4359_);
lean_dec_ref(v_a_4358_);
v_a_4485_ = lean_ctor_get(v___x_4378_, 0);
v_isSharedCheck_4492_ = !lean_is_exclusive(v___x_4378_);
if (v_isSharedCheck_4492_ == 0)
{
v___x_4487_ = v___x_4378_;
v_isShared_4488_ = v_isSharedCheck_4492_;
goto v_resetjp_4486_;
}
else
{
lean_inc(v_a_4485_);
lean_dec(v___x_4378_);
v___x_4487_ = lean_box(0);
v_isShared_4488_ = v_isSharedCheck_4492_;
goto v_resetjp_4486_;
}
v_resetjp_4486_:
{
lean_object* v___x_4490_; 
if (v_isShared_4488_ == 0)
{
v___x_4490_ = v___x_4487_;
goto v_reusejp_4489_;
}
else
{
lean_object* v_reuseFailAlloc_4491_; 
v_reuseFailAlloc_4491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4491_, 0, v_a_4485_);
v___x_4490_ = v_reuseFailAlloc_4491_;
goto v_reusejp_4489_;
}
v_reusejp_4489_:
{
return v___x_4490_;
}
}
}
}
else
{
lean_object* v_a_4493_; lean_object* v___x_4495_; uint8_t v_isShared_4496_; uint8_t v_isSharedCheck_4500_; 
lean_dec(v_a_4371_);
lean_dec(v___y_4366_);
lean_dec_ref(v___y_4365_);
lean_dec(v___y_4364_);
lean_dec_ref(v___y_4363_);
lean_dec_ref(v_xs_4361_);
lean_dec_ref(v___f_4360_);
lean_dec_ref(v___f_4359_);
lean_dec_ref(v_a_4358_);
v_a_4493_ = lean_ctor_get(v___x_4374_, 0);
v_isSharedCheck_4500_ = !lean_is_exclusive(v___x_4374_);
if (v_isSharedCheck_4500_ == 0)
{
v___x_4495_ = v___x_4374_;
v_isShared_4496_ = v_isSharedCheck_4500_;
goto v_resetjp_4494_;
}
else
{
lean_inc(v_a_4493_);
lean_dec(v___x_4374_);
v___x_4495_ = lean_box(0);
v_isShared_4496_ = v_isSharedCheck_4500_;
goto v_resetjp_4494_;
}
v_resetjp_4494_:
{
lean_object* v___x_4498_; 
if (v_isShared_4496_ == 0)
{
v___x_4498_ = v___x_4495_;
goto v_reusejp_4497_;
}
else
{
lean_object* v_reuseFailAlloc_4499_; 
v_reuseFailAlloc_4499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4499_, 0, v_a_4493_);
v___x_4498_ = v_reuseFailAlloc_4499_;
goto v_reusejp_4497_;
}
v_reusejp_4497_:
{
return v___x_4498_;
}
}
}
}
else
{
lean_object* v_a_4501_; lean_object* v___x_4503_; uint8_t v_isShared_4504_; uint8_t v_isSharedCheck_4508_; 
lean_dec(v___y_4366_);
lean_dec_ref(v___y_4365_);
lean_dec(v___y_4364_);
lean_dec_ref(v___y_4363_);
lean_dec_ref(v_xs_4361_);
lean_dec_ref(v___f_4360_);
lean_dec_ref(v___f_4359_);
lean_dec_ref(v_a_4358_);
v_a_4501_ = lean_ctor_get(v___x_4370_, 0);
v_isSharedCheck_4508_ = !lean_is_exclusive(v___x_4370_);
if (v_isSharedCheck_4508_ == 0)
{
v___x_4503_ = v___x_4370_;
v_isShared_4504_ = v_isSharedCheck_4508_;
goto v_resetjp_4502_;
}
else
{
lean_inc(v_a_4501_);
lean_dec(v___x_4370_);
v___x_4503_ = lean_box(0);
v_isShared_4504_ = v_isSharedCheck_4508_;
goto v_resetjp_4502_;
}
v_resetjp_4502_:
{
lean_object* v___x_4506_; 
if (v_isShared_4504_ == 0)
{
v___x_4506_ = v___x_4503_;
goto v_reusejp_4505_;
}
else
{
lean_object* v_reuseFailAlloc_4507_; 
v_reuseFailAlloc_4507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4507_, 0, v_a_4501_);
v___x_4506_ = v_reuseFailAlloc_4507_;
goto v_reusejp_4505_;
}
v_reusejp_4505_:
{
return v___x_4506_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preprocess___lam__0___boxed(lean_object* v___x_4509_, lean_object* v_a_4510_, lean_object* v___f_4511_, lean_object* v___f_4512_, lean_object* v_xs_4513_, lean_object* v_x_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_){
_start:
{
uint8_t v___x_14137__boxed_4520_; lean_object* v_res_4521_; 
v___x_14137__boxed_4520_ = lean_unbox(v___x_4509_);
v_res_4521_ = l_Lean_Elab_WF_preprocess___lam__0(v___x_14137__boxed_4520_, v_a_4510_, v___f_4511_, v___f_4512_, v_xs_4513_, v_x_4514_, v___y_4515_, v___y_4516_, v___y_4517_, v___y_4518_);
lean_dec_ref(v_x_4514_);
return v_res_4521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preprocess(lean_object* v_e_4523_, lean_object* v_a_4524_, lean_object* v_a_4525_, lean_object* v_a_4526_, lean_object* v_a_4527_){
_start:
{
lean_object* v_options_4529_; lean_object* v___x_4530_; uint8_t v___x_4531_; uint8_t v___x_4532_; 
v_options_4529_ = lean_ctor_get(v_a_4526_, 2);
v___x_4530_ = l_wf_preprocess;
v___x_4531_ = l_Lean_Option_get___at___00Lean_Elab_WF_preprocess_spec__1(v_options_4529_, v___x_4530_);
v___x_4532_ = 1;
if (v___x_4531_ == 0)
{
lean_object* v___x_4533_; lean_object* v___x_4534_; lean_object* v___x_4535_; 
lean_dec(v_a_4527_);
lean_dec_ref(v_a_4526_);
lean_dec(v_a_4525_);
lean_dec_ref(v_a_4524_);
v___x_4533_ = lean_box(0);
v___x_4534_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4534_, 0, v_e_4523_);
lean_ctor_set(v___x_4534_, 1, v___x_4533_);
lean_ctor_set_uint8(v___x_4534_, sizeof(void*)*2, v___x_4532_);
v___x_4535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4535_, 0, v___x_4534_);
return v___x_4535_;
}
else
{
lean_object* v___x_4536_; 
lean_inc(v_a_4527_);
lean_inc_ref(v_a_4526_);
lean_inc(v_a_4525_);
lean_inc_ref(v_a_4524_);
v___x_4536_ = l_Lean_Meta_letToHave(v_e_4523_, v_a_4524_, v_a_4525_, v_a_4526_, v_a_4527_);
if (lean_obj_tag(v___x_4536_) == 0)
{
lean_object* v_a_4537_; lean_object* v___f_4538_; lean_object* v___f_4539_; lean_object* v___x_4540_; lean_object* v___f_4541_; uint8_t v___x_4542_; lean_object* v___x_4543_; 
v_a_4537_ = lean_ctor_get(v___x_4536_, 0);
lean_inc(v_a_4537_);
lean_dec_ref(v___x_4536_);
v___f_4538_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___closed__0));
v___f_4539_ = ((lean_object*)(l_Lean_Elab_WF_preprocess___closed__0));
v___x_4540_ = lean_box(v___x_4532_);
lean_inc(v_a_4537_);
v___f_4541_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_preprocess___lam__0___boxed), 11, 4);
lean_closure_set(v___f_4541_, 0, v___x_4540_);
lean_closure_set(v___f_4541_, 1, v_a_4537_);
lean_closure_set(v___f_4541_, 2, v___f_4539_);
lean_closure_set(v___f_4541_, 3, v___f_4538_);
v___x_4542_ = 0;
v___x_4543_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__7___redArg(v_a_4537_, v___f_4541_, v___x_4542_, v_a_4524_, v_a_4525_, v_a_4526_, v_a_4527_);
return v___x_4543_;
}
else
{
lean_object* v_a_4544_; lean_object* v___x_4546_; uint8_t v_isShared_4547_; uint8_t v_isSharedCheck_4551_; 
lean_dec(v_a_4527_);
lean_dec_ref(v_a_4526_);
lean_dec(v_a_4525_);
lean_dec_ref(v_a_4524_);
v_a_4544_ = lean_ctor_get(v___x_4536_, 0);
v_isSharedCheck_4551_ = !lean_is_exclusive(v___x_4536_);
if (v_isSharedCheck_4551_ == 0)
{
v___x_4546_ = v___x_4536_;
v_isShared_4547_ = v_isSharedCheck_4551_;
goto v_resetjp_4545_;
}
else
{
lean_inc(v_a_4544_);
lean_dec(v___x_4536_);
v___x_4546_ = lean_box(0);
v_isShared_4547_ = v_isSharedCheck_4551_;
goto v_resetjp_4545_;
}
v_resetjp_4545_:
{
lean_object* v___x_4549_; 
if (v_isShared_4547_ == 0)
{
v___x_4549_ = v___x_4546_;
goto v_reusejp_4548_;
}
else
{
lean_object* v_reuseFailAlloc_4550_; 
v_reuseFailAlloc_4550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4550_, 0, v_a_4544_);
v___x_4549_ = v_reuseFailAlloc_4550_;
goto v_reusejp_4548_;
}
v_reusejp_4548_:
{
return v___x_4549_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preprocess___boxed(lean_object* v_e_4552_, lean_object* v_a_4553_, lean_object* v_a_4554_, lean_object* v_a_4555_, lean_object* v_a_4556_, lean_object* v_a_4557_){
_start:
{
lean_object* v_res_4558_; 
v_res_4558_ = l_Lean_Elab_WF_preprocess(v_e_4552_, v_a_4553_, v_a_4554_, v_a_4555_, v_a_4556_);
return v_res_4558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0(lean_object* v_x_4559_, lean_object* v_x_4560_, lean_object* v_x_4561_, lean_object* v___y_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_, lean_object* v___y_4565_){
_start:
{
lean_object* v___x_4567_; 
v___x_4567_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0___redArg(v_x_4559_, v_x_4560_, v_x_4561_);
return v___x_4567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0___boxed(lean_object* v_x_4568_, lean_object* v_x_4569_, lean_object* v_x_4570_, lean_object* v___y_4571_, lean_object* v___y_4572_, lean_object* v___y_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_){
_start:
{
lean_object* v_res_4576_; 
v_res_4576_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0(v_x_4568_, v_x_4569_, v_x_4570_, v___y_4571_, v___y_4572_, v___y_4573_, v___y_4574_);
lean_dec(v___y_4574_);
lean_dec_ref(v___y_4573_);
lean_dec(v___y_4572_);
lean_dec_ref(v___y_4571_);
return v_res_4576_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__10_spec__12(lean_object* v_00_u03b1_4577_, lean_object* v_ref_4578_, lean_object* v___y_4579_, lean_object* v___y_4580_){
_start:
{
lean_object* v___x_4582_; 
v___x_4582_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__10_spec__12___redArg(v_ref_4578_);
return v___x_4582_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__10_spec__12___boxed(lean_object* v_00_u03b1_4583_, lean_object* v_ref_4584_, lean_object* v___y_4585_, lean_object* v___y_4586_, lean_object* v___y_4587_){
_start:
{
lean_object* v_res_4588_; 
v_res_4588_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__10_spec__12(v_00_u03b1_4583_, v_ref_4584_, v___y_4585_, v___y_4586_);
lean_dec(v___y_4586_);
lean_dec_ref(v___y_4585_);
return v_res_4588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__10(lean_object* v_00_u03b1_4589_, lean_object* v_x_4590_, lean_object* v___y_4591_, lean_object* v___y_4592_, lean_object* v___y_4593_, lean_object* v___y_4594_, lean_object* v___y_4595_){
_start:
{
lean_object* v___x_4597_; 
v___x_4597_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__10___redArg(v_x_4590_, v___y_4591_, v___y_4592_, v___y_4593_, v___y_4594_, v___y_4595_);
return v___x_4597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__10___boxed(lean_object* v_00_u03b1_4598_, lean_object* v_x_4599_, lean_object* v___y_4600_, lean_object* v___y_4601_, lean_object* v___y_4602_, lean_object* v___y_4603_, lean_object* v___y_4604_, lean_object* v___y_4605_){
_start:
{
lean_object* v_res_4606_; 
v_res_4606_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__10(v_00_u03b1_4598_, v_x_4599_, v___y_4600_, v___y_4601_, v___y_4602_, v___y_4603_, v___y_4604_);
return v_res_4606_;
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
res = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__52_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12_();
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
