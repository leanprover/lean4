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
lean_object* lean_panic_fn(lean_object*, lean_object*);
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
lean_dec(v_a_192_);
lean_dec_ref(v_a_191_);
lean_dec(v_a_190_);
lean_dec_ref(v_a_189_);
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
lean_dec(v_a_297_);
lean_dec_ref(v_a_296_);
lean_dec(v_a_295_);
lean_dec_ref(v_a_294_);
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
lean_inc(v___y_335_);
lean_inc_ref(v___y_334_);
lean_inc(v___y_333_);
lean_inc_ref(v___y_332_);
lean_inc(v___y_329_);
lean_inc_ref(v___y_328_);
lean_inc(v___y_327_);
v___x_337_ = lean_apply_10(v_k_326_, v_b_330_, v_c_331_, v___y_327_, v___y_328_, v___y_329_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, lean_box(0));
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1___redArg___lam__0___boxed(lean_object* v_k_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v_b_342_, lean_object* v_c_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1___redArg___lam__0(v_k_338_, v___y_339_, v___y_340_, v___y_341_, v_b_342_, v_c_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_);
lean_dec(v___y_347_);
lean_dec_ref(v___y_346_);
lean_dec(v___y_345_);
lean_dec_ref(v___y_344_);
lean_dec(v___y_341_);
lean_dec_ref(v___y_340_);
lean_dec(v___y_339_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1___redArg(lean_object* v_e_350_, lean_object* v_k_351_, uint8_t v_cleanupAnnotations_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_){
_start:
{
lean_object* v___f_361_; uint8_t v___x_362_; uint8_t v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
lean_inc(v___y_355_);
lean_inc_ref(v___y_354_);
lean_inc(v___y_353_);
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
lean_dec(v___y_383_);
lean_dec_ref(v___y_382_);
lean_dec(v___y_381_);
lean_dec_ref(v___y_380_);
lean_dec(v___y_379_);
lean_dec_ref(v___y_378_);
lean_dec(v___y_377_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__0___redArg(size_t v_sz_414_, size_t v_i_415_, lean_object* v_bs_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_){
_start:
{
uint8_t v___x_422_; 
v___x_422_ = lean_usize_dec_lt(v_i_415_, v_sz_414_);
if (v___x_422_ == 0)
{
lean_object* v___x_423_; 
v___x_423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_423_, 0, v_bs_416_);
return v___x_423_;
}
else
{
lean_object* v_v_424_; lean_object* v___x_425_; 
v_v_424_ = lean_array_uget_borrowed(v_bs_416_, v_i_415_);
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
lean_dec(v___y_447_);
lean_dec_ref(v___y_446_);
lean_dec(v___y_445_);
lean_dec_ref(v___y_444_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__4___lam__0(uint8_t v___x_452_, lean_object* v_xs_453_, lean_object* v_body_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_){
_start:
{
size_t v_sz_463_; size_t v___x_464_; lean_object* v___x_465_; 
v_sz_463_ = lean_array_size(v_xs_453_);
v___x_464_ = ((size_t)0ULL);
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
lean_dec_ref(v_xs_453_);
return v___x_470_;
}
else
{
lean_object* v_a_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_478_; 
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
uint8_t v___x_21832__boxed_490_; lean_object* v_res_491_; 
v___x_21832__boxed_490_ = lean_unbox(v___x_479_);
v_res_491_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__4___lam__0(v___x_21832__boxed_490_, v_xs_480_, v_body_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_);
lean_dec(v___y_488_);
lean_dec_ref(v___y_487_);
lean_dec(v___y_486_);
lean_dec_ref(v___y_485_);
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
lean_dec(v___y_534_);
lean_dec_ref(v___y_533_);
lean_dec(v___y_532_);
lean_dec_ref(v___y_531_);
lean_dec(v___y_530_);
lean_dec_ref(v___y_529_);
lean_dec(v___y_528_);
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
lean_object* v_fileName_595_; lean_object* v_fileMap_596_; lean_object* v_options_597_; lean_object* v_currRecDepth_598_; lean_object* v_maxRecDepth_599_; lean_object* v_ref_600_; lean_object* v_currNamespace_601_; lean_object* v_openDecls_602_; lean_object* v_initHeartbeats_603_; lean_object* v_maxHeartbeats_604_; lean_object* v_quotContext_605_; lean_object* v_currMacroScope_606_; uint8_t v_diag_607_; lean_object* v_cancelTk_x3f_608_; uint8_t v_suppressElabErrors_609_; lean_object* v_inheritedTraceOptions_610_; lean_object* v_ref_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
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
v_ref_611_ = l_Lean_replaceRef(v_ref_585_, v_ref_600_);
lean_inc_ref(v_inheritedTraceOptions_610_);
lean_inc(v_cancelTk_x3f_608_);
lean_inc(v_currMacroScope_606_);
lean_inc(v_quotContext_605_);
lean_inc(v_maxHeartbeats_604_);
lean_inc(v_initHeartbeats_603_);
lean_inc(v_openDecls_602_);
lean_inc(v_currNamespace_601_);
lean_inc(v_maxRecDepth_599_);
lean_inc(v_currRecDepth_598_);
lean_inc_ref(v_options_597_);
lean_inc_ref(v_fileMap_596_);
lean_inc_ref(v_fileName_595_);
v___x_612_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_612_, 0, v_fileName_595_);
lean_ctor_set(v___x_612_, 1, v_fileMap_596_);
lean_ctor_set(v___x_612_, 2, v_options_597_);
lean_ctor_set(v___x_612_, 3, v_currRecDepth_598_);
lean_ctor_set(v___x_612_, 4, v_maxRecDepth_599_);
lean_ctor_set(v___x_612_, 5, v_ref_611_);
lean_ctor_set(v___x_612_, 6, v_currNamespace_601_);
lean_ctor_set(v___x_612_, 7, v_openDecls_602_);
lean_ctor_set(v___x_612_, 8, v_initHeartbeats_603_);
lean_ctor_set(v___x_612_, 9, v_maxHeartbeats_604_);
lean_ctor_set(v___x_612_, 10, v_quotContext_605_);
lean_ctor_set(v___x_612_, 11, v_currMacroScope_606_);
lean_ctor_set(v___x_612_, 12, v_cancelTk_x3f_608_);
lean_ctor_set(v___x_612_, 13, v_inheritedTraceOptions_610_);
lean_ctor_set_uint8(v___x_612_, sizeof(void*)*14, v_diag_607_);
lean_ctor_set_uint8(v___x_612_, sizeof(void*)*14 + 1, v_suppressElabErrors_609_);
v___x_613_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15___redArg(v_msg_586_, v___y_590_, v___y_591_, v___x_612_, v___y_593_);
lean_dec_ref(v___x_612_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13___redArg___boxed(lean_object* v_ref_614_, lean_object* v_msg_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13___redArg(v_ref_614_, v_msg_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_);
lean_dec(v___y_622_);
lean_dec_ref(v___y_621_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
lean_dec(v___y_616_);
lean_dec(v_ref_614_);
return v_res_624_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__0(void){
_start:
{
lean_object* v___x_625_; 
v___x_625_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_625_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__1(void){
_start:
{
lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_626_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__0);
v___x_627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_627_, 0, v___x_626_);
return v___x_627_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__2(void){
_start:
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_628_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_629_ = lean_unsigned_to_nat(0u);
v___x_630_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_630_, 0, v___x_629_);
lean_ctor_set(v___x_630_, 1, v___x_629_);
lean_ctor_set(v___x_630_, 2, v___x_629_);
lean_ctor_set(v___x_630_, 3, v___x_628_);
lean_ctor_set(v___x_630_, 4, v___x_628_);
lean_ctor_set(v___x_630_, 5, v___x_628_);
lean_ctor_set(v___x_630_, 6, v___x_628_);
lean_ctor_set(v___x_630_, 7, v___x_628_);
lean_ctor_set(v___x_630_, 8, v___x_628_);
return v___x_630_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__3(void){
_start:
{
lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_631_ = lean_unsigned_to_nat(32u);
v___x_632_ = lean_mk_empty_array_with_capacity(v___x_631_);
v___x_633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_633_, 0, v___x_632_);
return v___x_633_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__4(void){
_start:
{
size_t v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_634_ = ((size_t)5ULL);
v___x_635_ = lean_unsigned_to_nat(0u);
v___x_636_ = lean_unsigned_to_nat(32u);
v___x_637_ = lean_mk_empty_array_with_capacity(v___x_636_);
v___x_638_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__3);
v___x_639_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_639_, 0, v___x_638_);
lean_ctor_set(v___x_639_, 1, v___x_637_);
lean_ctor_set(v___x_639_, 2, v___x_635_);
lean_ctor_set(v___x_639_, 3, v___x_635_);
lean_ctor_set_usize(v___x_639_, 4, v___x_634_);
return v___x_639_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__5(void){
_start:
{
lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_640_ = lean_box(1);
v___x_641_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__4);
v___x_642_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_643_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_643_, 0, v___x_642_);
lean_ctor_set(v___x_643_, 1, v___x_641_);
lean_ctor_set(v___x_643_, 2, v___x_640_);
return v___x_643_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__7(void){
_start:
{
lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_645_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__6));
v___x_646_ = l_Lean_stringToMessageData(v___x_645_);
return v___x_646_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__9(void){
_start:
{
lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_648_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__8));
v___x_649_ = l_Lean_stringToMessageData(v___x_648_);
return v___x_649_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__11(void){
_start:
{
lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_651_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__10));
v___x_652_ = l_Lean_stringToMessageData(v___x_651_);
return v___x_652_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__13(void){
_start:
{
lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_654_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__12));
v___x_655_ = l_Lean_stringToMessageData(v___x_654_);
return v___x_655_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__15(void){
_start:
{
lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_657_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__14));
v___x_658_ = l_Lean_stringToMessageData(v___x_657_);
return v___x_658_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__17(void){
_start:
{
lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_660_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__16));
v___x_661_ = l_Lean_stringToMessageData(v___x_660_);
return v___x_661_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__19(void){
_start:
{
lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_663_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__18));
v___x_664_ = l_Lean_stringToMessageData(v___x_663_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg(lean_object* v_msg_665_, lean_object* v_declHint_666_, lean_object* v___y_667_){
_start:
{
lean_object* v___x_669_; lean_object* v_env_670_; uint8_t v___x_671_; 
v___x_669_ = lean_st_ref_get(v___y_667_);
v_env_670_ = lean_ctor_get(v___x_669_, 0);
lean_inc_ref(v_env_670_);
lean_dec(v___x_669_);
v___x_671_ = l_Lean_Name_isAnonymous(v_declHint_666_);
if (v___x_671_ == 0)
{
uint8_t v_isExporting_672_; 
v_isExporting_672_ = lean_ctor_get_uint8(v_env_670_, sizeof(void*)*8);
if (v_isExporting_672_ == 0)
{
lean_object* v___x_673_; 
lean_dec_ref(v_env_670_);
lean_dec(v_declHint_666_);
v___x_673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_673_, 0, v_msg_665_);
return v___x_673_;
}
else
{
lean_object* v___x_674_; uint8_t v___x_675_; 
lean_inc_ref(v_env_670_);
v___x_674_ = l_Lean_Environment_setExporting(v_env_670_, v___x_671_);
lean_inc(v_declHint_666_);
lean_inc_ref(v___x_674_);
v___x_675_ = l_Lean_Environment_contains(v___x_674_, v_declHint_666_, v_isExporting_672_);
if (v___x_675_ == 0)
{
lean_object* v___x_676_; 
lean_dec_ref(v___x_674_);
lean_dec_ref(v_env_670_);
lean_dec(v_declHint_666_);
v___x_676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_676_, 0, v_msg_665_);
return v___x_676_;
}
else
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v_c_682_; lean_object* v___x_683_; 
v___x_677_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__2);
v___x_678_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__5);
v___x_679_ = l_Lean_Options_empty;
v___x_680_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_680_, 0, v___x_674_);
lean_ctor_set(v___x_680_, 1, v___x_677_);
lean_ctor_set(v___x_680_, 2, v___x_678_);
lean_ctor_set(v___x_680_, 3, v___x_679_);
lean_inc(v_declHint_666_);
v___x_681_ = l_Lean_MessageData_ofConstName(v_declHint_666_, v___x_671_);
v_c_682_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_682_, 0, v___x_680_);
lean_ctor_set(v_c_682_, 1, v___x_681_);
v___x_683_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_670_, v_declHint_666_);
if (lean_obj_tag(v___x_683_) == 0)
{
lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
lean_dec_ref(v_env_670_);
lean_dec(v_declHint_666_);
v___x_684_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__7);
v___x_685_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_685_, 0, v___x_684_);
lean_ctor_set(v___x_685_, 1, v_c_682_);
v___x_686_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__9);
v___x_687_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_687_, 0, v___x_685_);
lean_ctor_set(v___x_687_, 1, v___x_686_);
v___x_688_ = l_Lean_MessageData_note(v___x_687_);
v___x_689_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_689_, 0, v_msg_665_);
lean_ctor_set(v___x_689_, 1, v___x_688_);
v___x_690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_690_, 0, v___x_689_);
return v___x_690_;
}
else
{
lean_object* v_val_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_726_; 
v_val_691_ = lean_ctor_get(v___x_683_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_683_);
if (v_isSharedCheck_726_ == 0)
{
v___x_693_ = v___x_683_;
v_isShared_694_ = v_isSharedCheck_726_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_val_691_);
lean_dec(v___x_683_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_726_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v_mod_698_; uint8_t v___x_699_; 
v___x_695_ = lean_box(0);
v___x_696_ = l_Lean_Environment_header(v_env_670_);
lean_dec_ref(v_env_670_);
v___x_697_ = l_Lean_EnvironmentHeader_moduleNames(v___x_696_);
v_mod_698_ = lean_array_get(v___x_695_, v___x_697_, v_val_691_);
lean_dec(v_val_691_);
lean_dec_ref(v___x_697_);
v___x_699_ = l_Lean_isPrivateName(v_declHint_666_);
lean_dec(v_declHint_666_);
if (v___x_699_ == 0)
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_711_; 
v___x_700_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__11);
v___x_701_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_701_, 0, v___x_700_);
lean_ctor_set(v___x_701_, 1, v_c_682_);
v___x_702_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__13);
v___x_703_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_703_, 0, v___x_701_);
lean_ctor_set(v___x_703_, 1, v___x_702_);
v___x_704_ = l_Lean_MessageData_ofName(v_mod_698_);
v___x_705_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_705_, 0, v___x_703_);
lean_ctor_set(v___x_705_, 1, v___x_704_);
v___x_706_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__15);
v___x_707_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_707_, 0, v___x_705_);
lean_ctor_set(v___x_707_, 1, v___x_706_);
v___x_708_ = l_Lean_MessageData_note(v___x_707_);
v___x_709_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_709_, 0, v_msg_665_);
lean_ctor_set(v___x_709_, 1, v___x_708_);
if (v_isShared_694_ == 0)
{
lean_ctor_set_tag(v___x_693_, 0);
lean_ctor_set(v___x_693_, 0, v___x_709_);
v___x_711_ = v___x_693_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v___x_709_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
else
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_724_; 
v___x_713_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__7);
v___x_714_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_714_, 0, v___x_713_);
lean_ctor_set(v___x_714_, 1, v_c_682_);
v___x_715_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__17);
v___x_716_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_716_, 0, v___x_714_);
lean_ctor_set(v___x_716_, 1, v___x_715_);
v___x_717_ = l_Lean_MessageData_ofName(v_mod_698_);
v___x_718_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_718_, 0, v___x_716_);
lean_ctor_set(v___x_718_, 1, v___x_717_);
v___x_719_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__19);
v___x_720_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_720_, 0, v___x_718_);
lean_ctor_set(v___x_720_, 1, v___x_719_);
v___x_721_ = l_Lean_MessageData_note(v___x_720_);
v___x_722_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_722_, 0, v_msg_665_);
lean_ctor_set(v___x_722_, 1, v___x_721_);
if (v_isShared_694_ == 0)
{
lean_ctor_set_tag(v___x_693_, 0);
lean_ctor_set(v___x_693_, 0, v___x_722_);
v___x_724_ = v___x_693_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v___x_722_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_727_; 
lean_dec_ref(v_env_670_);
lean_dec(v_declHint_666_);
v___x_727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_727_, 0, v_msg_665_);
return v___x_727_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___boxed(lean_object* v_msg_728_, lean_object* v_declHint_729_, lean_object* v___y_730_, lean_object* v___y_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg(v_msg_728_, v_declHint_729_, v___y_730_);
lean_dec(v___y_730_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12(lean_object* v_msg_733_, lean_object* v_declHint_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_){
_start:
{
lean_object* v___x_743_; lean_object* v_a_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_753_; 
v___x_743_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg(v_msg_733_, v_declHint_734_, v___y_741_);
v_a_744_ = lean_ctor_get(v___x_743_, 0);
v_isSharedCheck_753_ = !lean_is_exclusive(v___x_743_);
if (v_isSharedCheck_753_ == 0)
{
v___x_746_ = v___x_743_;
v_isShared_747_ = v_isSharedCheck_753_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_a_744_);
lean_dec(v___x_743_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_753_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_751_; 
v___x_748_ = l_Lean_unknownIdentifierMessageTag;
v___x_749_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_749_, 0, v___x_748_);
lean_ctor_set(v___x_749_, 1, v_a_744_);
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 0, v___x_749_);
v___x_751_ = v___x_746_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v___x_749_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
return v___x_751_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12___boxed(lean_object* v_msg_754_, lean_object* v_declHint_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12(v_msg_754_, v_declHint_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_);
lean_dec(v___y_762_);
lean_dec_ref(v___y_761_);
lean_dec(v___y_760_);
lean_dec_ref(v___y_759_);
lean_dec(v___y_758_);
lean_dec_ref(v___y_757_);
lean_dec(v___y_756_);
return v_res_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11___redArg(lean_object* v_ref_765_, lean_object* v_msg_766_, lean_object* v_declHint_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_){
_start:
{
lean_object* v___x_776_; lean_object* v_a_777_; lean_object* v___x_778_; 
v___x_776_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12(v_msg_766_, v_declHint_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_);
v_a_777_ = lean_ctor_get(v___x_776_, 0);
lean_inc(v_a_777_);
lean_dec_ref(v___x_776_);
v___x_778_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13___redArg(v_ref_765_, v_a_777_, v___y_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11___redArg___boxed(lean_object* v_ref_779_, lean_object* v_msg_780_, lean_object* v_declHint_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_){
_start:
{
lean_object* v_res_790_; 
v_res_790_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11___redArg(v_ref_779_, v_msg_780_, v_declHint_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_);
lean_dec(v___y_788_);
lean_dec_ref(v___y_787_);
lean_dec(v___y_786_);
lean_dec_ref(v___y_785_);
lean_dec(v___y_784_);
lean_dec_ref(v___y_783_);
lean_dec(v___y_782_);
lean_dec(v_ref_779_);
return v_res_790_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_792_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__0));
v___x_793_ = l_Lean_stringToMessageData(v___x_792_);
return v___x_793_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_795_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__2));
v___x_796_ = l_Lean_stringToMessageData(v___x_795_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg(lean_object* v_ref_797_, lean_object* v_constName_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_){
_start:
{
lean_object* v___x_807_; uint8_t v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_807_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__1);
v___x_808_ = 0;
lean_inc(v_constName_798_);
v___x_809_ = l_Lean_MessageData_ofConstName(v_constName_798_, v___x_808_);
v___x_810_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_810_, 0, v___x_807_);
lean_ctor_set(v___x_810_, 1, v___x_809_);
v___x_811_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__3);
v___x_812_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_812_, 0, v___x_810_);
lean_ctor_set(v___x_812_, 1, v___x_811_);
v___x_813_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11___redArg(v_ref_797_, v___x_812_, v_constName_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___boxed(lean_object* v_ref_814_, lean_object* v_constName_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg(v_ref_814_, v_constName_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_);
lean_dec(v___y_822_);
lean_dec_ref(v___y_821_);
lean_dec(v___y_820_);
lean_dec_ref(v___y_819_);
lean_dec(v___y_818_);
lean_dec_ref(v___y_817_);
lean_dec(v___y_816_);
lean_dec(v_ref_814_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3___redArg(lean_object* v_constName_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_){
_start:
{
lean_object* v_ref_834_; lean_object* v___x_835_; 
v_ref_834_ = lean_ctor_get(v___y_831_, 5);
v___x_835_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg(v_ref_834_, v_constName_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3___redArg___boxed(lean_object* v_constName_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3___redArg(v_constName_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_);
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
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2(lean_object* v_constName_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_){
_start:
{
lean_object* v___x_855_; lean_object* v_env_856_; uint8_t v___x_857_; lean_object* v___x_858_; 
v___x_855_ = lean_st_ref_get(v___y_853_);
v_env_856_ = lean_ctor_get(v___x_855_, 0);
lean_inc_ref(v_env_856_);
lean_dec(v___x_855_);
v___x_857_ = 0;
lean_inc(v_constName_846_);
v___x_858_ = l_Lean_Environment_find_x3f(v_env_856_, v_constName_846_, v___x_857_);
if (lean_obj_tag(v___x_858_) == 0)
{
lean_object* v___x_859_; 
v___x_859_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3___redArg(v_constName_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_);
return v___x_859_;
}
else
{
lean_object* v_val_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_867_; 
lean_dec(v_constName_846_);
v_val_860_ = lean_ctor_get(v___x_858_, 0);
v_isSharedCheck_867_ = !lean_is_exclusive(v___x_858_);
if (v_isSharedCheck_867_ == 0)
{
v___x_862_ = v___x_858_;
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_val_860_);
lean_dec(v___x_858_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v___x_865_; 
if (v_isShared_863_ == 0)
{
lean_ctor_set_tag(v___x_862_, 0);
v___x_865_ = v___x_862_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v_val_860_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2___boxed(lean_object* v_constName_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2(v_constName_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_);
lean_dec(v___y_875_);
lean_dec_ref(v___y_874_);
lean_dec(v___y_873_);
lean_dec_ref(v___y_872_);
lean_dec(v___y_871_);
lean_dec_ref(v___y_870_);
lean_dec(v___y_869_);
return v_res_877_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___closed__0(void){
_start:
{
lean_object* v___x_878_; 
v___x_878_ = l_instMonadEIO(lean_box(0));
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3(lean_object* v_msg_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_){
_start:
{
lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v_toApplicative_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_958_; 
v___x_892_ = lean_obj_once(&l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___closed__0, &l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___closed__0_once, _init_l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___closed__0);
v___x_893_ = l_StateRefT_x27_instMonad___redArg(v___x_892_);
v_toApplicative_894_ = lean_ctor_get(v___x_893_, 0);
v_isSharedCheck_958_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_958_ == 0)
{
lean_object* v_unused_959_; 
v_unused_959_ = lean_ctor_get(v___x_893_, 1);
lean_dec(v_unused_959_);
v___x_896_ = v___x_893_;
v_isShared_897_ = v_isSharedCheck_958_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_toApplicative_894_);
lean_dec(v___x_893_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_958_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v_toFunctor_898_; lean_object* v_toSeq_899_; lean_object* v_toSeqLeft_900_; lean_object* v_toSeqRight_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_956_; 
v_toFunctor_898_ = lean_ctor_get(v_toApplicative_894_, 0);
v_toSeq_899_ = lean_ctor_get(v_toApplicative_894_, 2);
v_toSeqLeft_900_ = lean_ctor_get(v_toApplicative_894_, 3);
v_toSeqRight_901_ = lean_ctor_get(v_toApplicative_894_, 4);
v_isSharedCheck_956_ = !lean_is_exclusive(v_toApplicative_894_);
if (v_isSharedCheck_956_ == 0)
{
lean_object* v_unused_957_; 
v_unused_957_ = lean_ctor_get(v_toApplicative_894_, 1);
lean_dec(v_unused_957_);
v___x_903_ = v_toApplicative_894_;
v_isShared_904_ = v_isSharedCheck_956_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_toSeqRight_901_);
lean_inc(v_toSeqLeft_900_);
lean_inc(v_toSeq_899_);
lean_inc(v_toFunctor_898_);
lean_dec(v_toApplicative_894_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_956_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v___f_905_; lean_object* v___f_906_; lean_object* v___f_907_; lean_object* v___f_908_; lean_object* v___x_909_; lean_object* v___f_910_; lean_object* v___f_911_; lean_object* v___f_912_; lean_object* v___x_914_; 
v___f_905_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___closed__1));
v___f_906_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___closed__2));
lean_inc_ref(v_toFunctor_898_);
v___f_907_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_907_, 0, v_toFunctor_898_);
v___f_908_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_908_, 0, v_toFunctor_898_);
v___x_909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_909_, 0, v___f_907_);
lean_ctor_set(v___x_909_, 1, v___f_908_);
v___f_910_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_910_, 0, v_toSeqRight_901_);
v___f_911_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_911_, 0, v_toSeqLeft_900_);
v___f_912_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_912_, 0, v_toSeq_899_);
if (v_isShared_904_ == 0)
{
lean_ctor_set(v___x_903_, 4, v___f_910_);
lean_ctor_set(v___x_903_, 3, v___f_911_);
lean_ctor_set(v___x_903_, 2, v___f_912_);
lean_ctor_set(v___x_903_, 1, v___f_905_);
lean_ctor_set(v___x_903_, 0, v___x_909_);
v___x_914_ = v___x_903_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v___x_909_);
lean_ctor_set(v_reuseFailAlloc_955_, 1, v___f_905_);
lean_ctor_set(v_reuseFailAlloc_955_, 2, v___f_912_);
lean_ctor_set(v_reuseFailAlloc_955_, 3, v___f_911_);
lean_ctor_set(v_reuseFailAlloc_955_, 4, v___f_910_);
v___x_914_ = v_reuseFailAlloc_955_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
lean_object* v___x_916_; 
if (v_isShared_897_ == 0)
{
lean_ctor_set(v___x_896_, 1, v___f_906_);
lean_ctor_set(v___x_896_, 0, v___x_914_);
v___x_916_ = v___x_896_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v___x_914_);
lean_ctor_set(v_reuseFailAlloc_954_, 1, v___f_906_);
v___x_916_ = v_reuseFailAlloc_954_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
lean_object* v___x_917_; lean_object* v_toApplicative_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_952_; 
v___x_917_ = l_StateRefT_x27_instMonad___redArg(v___x_916_);
v_toApplicative_918_ = lean_ctor_get(v___x_917_, 0);
v_isSharedCheck_952_ = !lean_is_exclusive(v___x_917_);
if (v_isSharedCheck_952_ == 0)
{
lean_object* v_unused_953_; 
v_unused_953_ = lean_ctor_get(v___x_917_, 1);
lean_dec(v_unused_953_);
v___x_920_ = v___x_917_;
v_isShared_921_ = v_isSharedCheck_952_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_toApplicative_918_);
lean_dec(v___x_917_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_952_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v_toFunctor_922_; lean_object* v_toSeq_923_; lean_object* v_toSeqLeft_924_; lean_object* v_toSeqRight_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_950_; 
v_toFunctor_922_ = lean_ctor_get(v_toApplicative_918_, 0);
v_toSeq_923_ = lean_ctor_get(v_toApplicative_918_, 2);
v_toSeqLeft_924_ = lean_ctor_get(v_toApplicative_918_, 3);
v_toSeqRight_925_ = lean_ctor_get(v_toApplicative_918_, 4);
v_isSharedCheck_950_ = !lean_is_exclusive(v_toApplicative_918_);
if (v_isSharedCheck_950_ == 0)
{
lean_object* v_unused_951_; 
v_unused_951_ = lean_ctor_get(v_toApplicative_918_, 1);
lean_dec(v_unused_951_);
v___x_927_ = v_toApplicative_918_;
v_isShared_928_ = v_isSharedCheck_950_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_toSeqRight_925_);
lean_inc(v_toSeqLeft_924_);
lean_inc(v_toSeq_923_);
lean_inc(v_toFunctor_922_);
lean_dec(v_toApplicative_918_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_950_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___f_929_; lean_object* v___f_930_; lean_object* v___f_931_; lean_object* v___f_932_; lean_object* v___x_933_; lean_object* v___f_934_; lean_object* v___f_935_; lean_object* v___f_936_; lean_object* v___x_938_; 
v___f_929_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___closed__3));
v___f_930_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___closed__4));
lean_inc_ref(v_toFunctor_922_);
v___f_931_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_931_, 0, v_toFunctor_922_);
v___f_932_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_932_, 0, v_toFunctor_922_);
v___x_933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_933_, 0, v___f_931_);
lean_ctor_set(v___x_933_, 1, v___f_932_);
v___f_934_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_934_, 0, v_toSeqRight_925_);
v___f_935_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_935_, 0, v_toSeqLeft_924_);
v___f_936_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_936_, 0, v_toSeq_923_);
if (v_isShared_928_ == 0)
{
lean_ctor_set(v___x_927_, 4, v___f_934_);
lean_ctor_set(v___x_927_, 3, v___f_935_);
lean_ctor_set(v___x_927_, 2, v___f_936_);
lean_ctor_set(v___x_927_, 1, v___f_929_);
lean_ctor_set(v___x_927_, 0, v___x_933_);
v___x_938_ = v___x_927_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v___x_933_);
lean_ctor_set(v_reuseFailAlloc_949_, 1, v___f_929_);
lean_ctor_set(v_reuseFailAlloc_949_, 2, v___f_936_);
lean_ctor_set(v_reuseFailAlloc_949_, 3, v___f_935_);
lean_ctor_set(v_reuseFailAlloc_949_, 4, v___f_934_);
v___x_938_ = v_reuseFailAlloc_949_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
lean_object* v___x_940_; 
if (v_isShared_921_ == 0)
{
lean_ctor_set(v___x_920_, 1, v___f_930_);
lean_ctor_set(v___x_920_, 0, v___x_938_);
v___x_940_ = v___x_920_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v___x_938_);
lean_ctor_set(v_reuseFailAlloc_948_, 1, v___f_930_);
v___x_940_ = v_reuseFailAlloc_948_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_13749__overap_946_; lean_object* v___x_947_; 
v___x_941_ = l_StateRefT_x27_instMonad___redArg(v___x_940_);
v___x_942_ = l_ReaderT_instMonad___redArg(v___x_941_);
v___x_943_ = l_ReaderT_instMonad___redArg(v___x_942_);
v___x_944_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_945_ = l_instInhabitedOfMonad___redArg(v___x_943_, v___x_944_);
v___x_13749__overap_946_ = lean_panic_fn(v___x_945_, v_msg_883_);
lean_inc(v___y_890_);
lean_inc_ref(v___y_889_);
lean_inc(v___y_888_);
lean_inc_ref(v___y_887_);
lean_inc(v___y_886_);
lean_inc_ref(v___y_885_);
lean_inc(v___y_884_);
v___x_947_ = lean_apply_8(v___x_13749__overap_946_, v___y_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_, lean_box(0));
return v___x_947_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___boxed(lean_object* v_msg_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3(v_msg_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_);
lean_dec(v___y_967_);
lean_dec_ref(v___y_966_);
lean_dec(v___y_965_);
lean_dec_ref(v___y_964_);
lean_dec(v___y_963_);
lean_dec_ref(v___y_962_);
lean_dec(v___y_961_);
return v_res_969_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5___closed__3(void){
_start:
{
lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_973_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5___closed__2));
v___x_974_ = lean_unsigned_to_nat(53u);
v___x_975_ = lean_unsigned_to_nat(62u);
v___x_976_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5___closed__1));
v___x_977_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5___closed__0));
v___x_978_ = l_mkPanicMessageWithDecl(v___x_977_, v___x_976_, v___x_975_, v___x_974_, v___x_973_);
return v___x_978_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5(size_t v_sz_979_, size_t v_i_980_, lean_object* v_bs_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_){
_start:
{
uint8_t v___x_990_; 
v___x_990_ = lean_usize_dec_lt(v_i_980_, v_sz_979_);
if (v___x_990_ == 0)
{
lean_object* v___x_991_; 
v___x_991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_991_, 0, v_bs_981_);
return v___x_991_;
}
else
{
lean_object* v_v_992_; lean_object* v___x_993_; 
v_v_992_ = lean_array_uget_borrowed(v_bs_981_, v_i_980_);
lean_inc(v_v_992_);
v___x_993_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2(v_v_992_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_);
if (lean_obj_tag(v___x_993_) == 0)
{
lean_object* v_a_994_; lean_object* v___x_995_; lean_object* v_bs_x27_996_; lean_object* v_a_998_; 
v_a_994_ = lean_ctor_get(v___x_993_, 0);
lean_inc(v_a_994_);
lean_dec_ref(v___x_993_);
v___x_995_ = lean_unsigned_to_nat(0u);
v_bs_x27_996_ = lean_array_uset(v_bs_981_, v_i_980_, v___x_995_);
if (lean_obj_tag(v_a_994_) == 6)
{
lean_object* v_val_1003_; lean_object* v_numFields_1004_; uint8_t v___x_1005_; lean_object* v___x_1006_; 
v_val_1003_ = lean_ctor_get(v_a_994_, 0);
lean_inc_ref(v_val_1003_);
lean_dec_ref(v_a_994_);
v_numFields_1004_ = lean_ctor_get(v_val_1003_, 4);
lean_inc(v_numFields_1004_);
lean_dec_ref(v_val_1003_);
v___x_1005_ = 0;
v___x_1006_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1006_, 0, v_numFields_1004_);
lean_ctor_set(v___x_1006_, 1, v___x_995_);
lean_ctor_set_uint8(v___x_1006_, sizeof(void*)*2, v___x_1005_);
v_a_998_ = v___x_1006_;
goto v___jp_997_;
}
else
{
lean_object* v___x_1007_; lean_object* v___x_1008_; 
lean_dec(v_a_994_);
v___x_1007_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5___closed__3);
v___x_1008_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3(v___x_1007_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_);
if (lean_obj_tag(v___x_1008_) == 0)
{
lean_object* v_a_1009_; 
v_a_1009_ = lean_ctor_get(v___x_1008_, 0);
lean_inc(v_a_1009_);
lean_dec_ref(v___x_1008_);
v_a_998_ = v_a_1009_;
goto v___jp_997_;
}
else
{
lean_object* v_a_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1017_; 
lean_dec_ref(v_bs_x27_996_);
v_a_1010_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1012_ = v___x_1008_;
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_a_1010_);
lean_dec(v___x_1008_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v___x_1015_; 
if (v_isShared_1013_ == 0)
{
v___x_1015_ = v___x_1012_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_a_1010_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
}
}
}
}
v___jp_997_:
{
size_t v___x_999_; size_t v___x_1000_; lean_object* v___x_1001_; 
v___x_999_ = ((size_t)1ULL);
v___x_1000_ = lean_usize_add(v_i_980_, v___x_999_);
v___x_1001_ = lean_array_uset(v_bs_x27_996_, v_i_980_, v_a_998_);
v_i_980_ = v___x_1000_;
v_bs_981_ = v___x_1001_;
goto _start;
}
}
else
{
lean_object* v_a_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1025_; 
lean_dec_ref(v_bs_981_);
v_a_1018_ = lean_ctor_get(v___x_993_, 0);
v_isSharedCheck_1025_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1020_ = v___x_993_;
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_a_1018_);
lean_dec(v___x_993_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v___x_1023_; 
if (v_isShared_1021_ == 0)
{
v___x_1023_ = v___x_1020_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_a_1018_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
return v___x_1023_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5___boxed(lean_object* v_sz_1026_, lean_object* v_i_1027_, lean_object* v_bs_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_){
_start:
{
size_t v_sz_boxed_1037_; size_t v_i_boxed_1038_; lean_object* v_res_1039_; 
v_sz_boxed_1037_ = lean_unbox_usize(v_sz_1026_);
lean_dec(v_sz_1026_);
v_i_boxed_1038_ = lean_unbox_usize(v_i_1027_);
lean_dec(v_i_1027_);
v_res_1039_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5(v_sz_boxed_1037_, v_i_boxed_1038_, v_bs_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_);
lean_dec(v___y_1035_);
lean_dec_ref(v___y_1034_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
lean_dec(v___y_1031_);
lean_dec_ref(v___y_1030_);
lean_dec(v___y_1029_);
return v_res_1039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__4___redArg(lean_object* v_declName_1040_, lean_object* v___y_1041_){
_start:
{
lean_object* v___x_1043_; lean_object* v_env_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1043_ = lean_st_ref_get(v___y_1041_);
v_env_1044_ = lean_ctor_get(v___x_1043_, 0);
lean_inc_ref(v_env_1044_);
lean_dec(v___x_1043_);
v___x_1045_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_1044_, v_declName_1040_);
v___x_1046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1045_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__4___redArg___boxed(lean_object* v_declName_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__4___redArg(v_declName_1047_, v___y_1048_);
lean_dec(v___y_1048_);
return v_res_1050_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1051_; lean_object* v_dummy_1052_; 
v___x_1051_ = lean_box(0);
v_dummy_1052_ = l_Lean_Expr_sort___override(v___x_1051_);
return v_dummy_1052_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; 
v___x_1053_ = lean_box(0);
v___x_1054_ = lean_unsigned_to_nat(16u);
v___x_1055_ = lean_mk_array(v___x_1054_, v___x_1053_);
return v___x_1055_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1056_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__1, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__1_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__1);
v___x_1057_ = lean_unsigned_to_nat(0u);
v___x_1058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1057_);
lean_ctor_set(v___x_1058_, 1, v___x_1056_);
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2(lean_object* v_e_1061_, uint8_t v_alsoCasesOn_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_){
_start:
{
uint8_t v___x_1074_; 
v___x_1074_ = l_Lean_Expr_isApp(v_e_1061_);
if (v___x_1074_ == 0)
{
lean_object* v___x_1075_; lean_object* v___x_1076_; 
lean_dec_ref(v_e_1061_);
v___x_1075_ = lean_box(0);
v___x_1076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1075_);
return v___x_1076_;
}
else
{
lean_object* v___x_1077_; 
v___x_1077_ = l_Lean_Expr_getAppFn(v_e_1061_);
if (lean_obj_tag(v___x_1077_) == 4)
{
lean_object* v_declName_1078_; lean_object* v_us_1079_; lean_object* v___x_1080_; lean_object* v_a_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1235_; 
v_declName_1078_ = lean_ctor_get(v___x_1077_, 0);
lean_inc(v_declName_1078_);
v_us_1079_ = lean_ctor_get(v___x_1077_, 1);
lean_inc(v_us_1079_);
lean_dec_ref(v___x_1077_);
lean_inc(v_declName_1078_);
v___x_1080_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__4___redArg(v_declName_1078_, v___y_1069_);
v_a_1081_ = lean_ctor_get(v___x_1080_, 0);
v_isSharedCheck_1235_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1235_ == 0)
{
v___x_1083_ = v___x_1080_;
v_isShared_1084_ = v_isSharedCheck_1235_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_a_1081_);
lean_dec(v___x_1080_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1235_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
if (lean_obj_tag(v_a_1081_) == 1)
{
lean_object* v_val_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1127_; 
v_val_1085_ = lean_ctor_get(v_a_1081_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v_a_1081_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1087_ = v_a_1081_;
v_isShared_1088_ = v_isSharedCheck_1127_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_val_1085_);
lean_dec(v_a_1081_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1127_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v_dummy_1089_; lean_object* v_nargs_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v_args_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; uint8_t v___x_1097_; 
v_dummy_1089_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0);
v_nargs_1090_ = l_Lean_Expr_getAppNumArgs(v_e_1061_);
lean_inc(v_nargs_1090_);
v___x_1091_ = lean_mk_array(v_nargs_1090_, v_dummy_1089_);
v___x_1092_ = lean_unsigned_to_nat(1u);
v___x_1093_ = lean_nat_sub(v_nargs_1090_, v___x_1092_);
lean_dec(v_nargs_1090_);
v_args_1094_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1061_, v___x_1091_, v___x_1093_);
v___x_1095_ = lean_array_get_size(v_args_1094_);
v___x_1096_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_1085_);
v___x_1097_ = lean_nat_dec_lt(v___x_1095_, v___x_1096_);
lean_dec(v___x_1096_);
if (v___x_1097_ == 0)
{
lean_object* v_numParams_1098_; lean_object* v_numDiscrs_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1118_; 
v_numParams_1098_ = lean_ctor_get(v_val_1085_, 0);
v_numDiscrs_1099_ = lean_ctor_get(v_val_1085_, 1);
v___x_1100_ = lean_array_mk(v_us_1079_);
v___x_1101_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1098_);
v___x_1102_ = l_Array_extract___redArg(v_args_1094_, v___x_1101_, v_numParams_1098_);
v___x_1103_ = l_Lean_instInhabitedExpr;
v___x_1104_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_1085_);
v___x_1105_ = lean_array_get(v___x_1103_, v_args_1094_, v___x_1104_);
lean_dec(v___x_1104_);
v___x_1106_ = lean_nat_add(v_numParams_1098_, v___x_1092_);
v___x_1107_ = lean_nat_add(v___x_1106_, v_numDiscrs_1099_);
lean_inc(v___x_1107_);
lean_inc_ref(v_args_1094_);
v___x_1108_ = l_Array_toSubarray___redArg(v_args_1094_, v___x_1106_, v___x_1107_);
v___x_1109_ = l_Subarray_copy___redArg(v___x_1108_);
v___x_1110_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_1085_);
v___x_1111_ = lean_nat_add(v___x_1107_, v___x_1110_);
lean_dec(v___x_1110_);
lean_inc(v___x_1111_);
lean_inc_ref(v_args_1094_);
v___x_1112_ = l_Array_toSubarray___redArg(v_args_1094_, v___x_1107_, v___x_1111_);
v___x_1113_ = l_Subarray_copy___redArg(v___x_1112_);
v___x_1114_ = l_Array_toSubarray___redArg(v_args_1094_, v___x_1111_, v___x_1095_);
v___x_1115_ = l_Subarray_copy___redArg(v___x_1114_);
v___x_1116_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1116_, 0, v_val_1085_);
lean_ctor_set(v___x_1116_, 1, v_declName_1078_);
lean_ctor_set(v___x_1116_, 2, v___x_1100_);
lean_ctor_set(v___x_1116_, 3, v___x_1102_);
lean_ctor_set(v___x_1116_, 4, v___x_1105_);
lean_ctor_set(v___x_1116_, 5, v___x_1109_);
lean_ctor_set(v___x_1116_, 6, v___x_1113_);
lean_ctor_set(v___x_1116_, 7, v___x_1115_);
if (v_isShared_1088_ == 0)
{
lean_ctor_set(v___x_1087_, 0, v___x_1116_);
v___x_1118_ = v___x_1087_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v___x_1116_);
v___x_1118_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
lean_object* v___x_1120_; 
if (v_isShared_1084_ == 0)
{
lean_ctor_set(v___x_1083_, 0, v___x_1118_);
v___x_1120_ = v___x_1083_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v___x_1118_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
return v___x_1120_;
}
}
}
else
{
lean_object* v___x_1123_; lean_object* v___x_1125_; 
lean_dec_ref(v_args_1094_);
lean_del_object(v___x_1087_);
lean_dec(v_val_1085_);
lean_dec(v_us_1079_);
lean_dec(v_declName_1078_);
v___x_1123_ = lean_box(0);
if (v_isShared_1084_ == 0)
{
lean_ctor_set(v___x_1083_, 0, v___x_1123_);
v___x_1125_ = v___x_1083_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v___x_1123_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
}
}
else
{
lean_object* v___x_1128_; 
lean_del_object(v___x_1083_);
lean_dec(v_a_1081_);
v___x_1128_ = lean_st_ref_get(v___y_1069_);
if (v_alsoCasesOn_1062_ == 0)
{
lean_dec(v___x_1128_);
lean_dec(v_us_1079_);
lean_dec(v_declName_1078_);
lean_dec_ref(v_e_1061_);
goto v___jp_1071_;
}
else
{
lean_object* v_env_1129_; uint8_t v___x_1130_; 
v_env_1129_ = lean_ctor_get(v___x_1128_, 0);
lean_inc_ref(v_env_1129_);
lean_dec(v___x_1128_);
lean_inc(v_declName_1078_);
v___x_1130_ = l_Lean_isCasesOnRecursor(v_env_1129_, v_declName_1078_);
if (v___x_1130_ == 0)
{
lean_dec(v_us_1079_);
lean_dec(v_declName_1078_);
lean_dec_ref(v_e_1061_);
goto v___jp_1071_;
}
else
{
lean_object* v_indName_1131_; lean_object* v___x_1132_; 
v_indName_1131_ = l_Lean_Name_getPrefix(v_declName_1078_);
v___x_1132_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2(v_indName_1131_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_);
if (lean_obj_tag(v___x_1132_) == 0)
{
lean_object* v_a_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1226_; 
v_a_1133_ = lean_ctor_get(v___x_1132_, 0);
v_isSharedCheck_1226_ = !lean_is_exclusive(v___x_1132_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1135_ = v___x_1132_;
v_isShared_1136_ = v_isSharedCheck_1226_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_a_1133_);
lean_dec(v___x_1132_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1226_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
if (lean_obj_tag(v_a_1133_) == 5)
{
lean_object* v_val_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1221_; 
v_val_1137_ = lean_ctor_get(v_a_1133_, 0);
v_isSharedCheck_1221_ = !lean_is_exclusive(v_a_1133_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1139_ = v_a_1133_;
v_isShared_1140_ = v_isSharedCheck_1221_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_val_1137_);
lean_dec(v_a_1133_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1221_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v_toConstantVal_1141_; lean_object* v_numParams_1142_; lean_object* v_numIndices_1143_; lean_object* v_ctors_1144_; lean_object* v_nargs_1145_; lean_object* v_dummy_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v_args_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; uint8_t v___x_1157_; 
v_toConstantVal_1141_ = lean_ctor_get(v_val_1137_, 0);
lean_inc_ref(v_toConstantVal_1141_);
v_numParams_1142_ = lean_ctor_get(v_val_1137_, 1);
lean_inc(v_numParams_1142_);
v_numIndices_1143_ = lean_ctor_get(v_val_1137_, 2);
lean_inc(v_numIndices_1143_);
v_ctors_1144_ = lean_ctor_get(v_val_1137_, 4);
lean_inc(v_ctors_1144_);
v_nargs_1145_ = l_Lean_Expr_getAppNumArgs(v_e_1061_);
v_dummy_1146_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0);
lean_inc(v_nargs_1145_);
v___x_1147_ = lean_mk_array(v_nargs_1145_, v_dummy_1146_);
v___x_1148_ = lean_unsigned_to_nat(1u);
v___x_1149_ = lean_nat_sub(v_nargs_1145_, v___x_1148_);
lean_dec(v_nargs_1145_);
v_args_1150_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1061_, v___x_1147_, v___x_1149_);
v___x_1151_ = lean_nat_add(v_numParams_1142_, v___x_1148_);
v___x_1152_ = lean_nat_add(v___x_1151_, v_numIndices_1143_);
v___x_1153_ = lean_nat_add(v___x_1152_, v___x_1148_);
lean_dec(v___x_1152_);
v___x_1154_ = l_Lean_InductiveVal_numCtors(v_val_1137_);
lean_dec_ref(v_val_1137_);
v___x_1155_ = lean_nat_add(v___x_1153_, v___x_1154_);
lean_dec(v___x_1154_);
v___x_1156_ = lean_array_get_size(v_args_1150_);
v___x_1157_ = lean_nat_dec_le(v___x_1155_, v___x_1156_);
if (v___x_1157_ == 0)
{
lean_object* v___x_1158_; lean_object* v___x_1160_; 
lean_dec(v___x_1155_);
lean_dec(v___x_1153_);
lean_dec(v___x_1151_);
lean_dec_ref(v_args_1150_);
lean_dec(v_ctors_1144_);
lean_dec(v_numIndices_1143_);
lean_dec(v_numParams_1142_);
lean_dec_ref(v_toConstantVal_1141_);
lean_del_object(v___x_1139_);
lean_dec(v_us_1079_);
lean_dec(v_declName_1078_);
v___x_1158_ = lean_box(0);
if (v_isShared_1136_ == 0)
{
lean_ctor_set(v___x_1135_, 0, v___x_1158_);
v___x_1160_ = v___x_1135_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v___x_1158_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
return v___x_1160_;
}
}
else
{
lean_object* v___x_1162_; lean_object* v_params_1163_; lean_object* v___x_1164_; lean_object* v_motive_1165_; lean_object* v_discrs_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v_discrInfos_1169_; lean_object* v_alts_1170_; lean_object* v___y_1172_; lean_object* v___y_1173_; lean_object* v_lower_1212_; lean_object* v_upper_1213_; uint8_t v___x_1220_; 
lean_del_object(v___x_1135_);
v___x_1162_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1142_);
lean_inc_ref(v_args_1150_);
v_params_1163_ = l_Array_toSubarray___redArg(v_args_1150_, v___x_1162_, v_numParams_1142_);
v___x_1164_ = l_Lean_instInhabitedExpr;
v_motive_1165_ = lean_array_get(v___x_1164_, v_args_1150_, v_numParams_1142_);
lean_dec(v_numParams_1142_);
lean_inc(v___x_1153_);
lean_inc_ref(v_args_1150_);
v_discrs_1166_ = l_Array_toSubarray___redArg(v_args_1150_, v___x_1151_, v___x_1153_);
v___x_1167_ = lean_nat_add(v_numIndices_1143_, v___x_1148_);
lean_dec(v_numIndices_1143_);
v___x_1168_ = lean_box(0);
v_discrInfos_1169_ = lean_mk_array(v___x_1167_, v___x_1168_);
lean_inc(v___x_1155_);
lean_inc_ref(v_args_1150_);
v_alts_1170_ = l_Array_toSubarray___redArg(v_args_1150_, v___x_1153_, v___x_1155_);
v___x_1220_ = lean_nat_dec_le(v___x_1155_, v___x_1162_);
if (v___x_1220_ == 0)
{
v_lower_1212_ = v___x_1155_;
v_upper_1213_ = v___x_1156_;
goto v___jp_1211_;
}
else
{
lean_dec(v___x_1155_);
v_lower_1212_ = v___x_1162_;
v_upper_1213_ = v___x_1156_;
goto v___jp_1211_;
}
v___jp_1171_:
{
lean_object* v___x_1174_; size_t v_sz_1175_; size_t v___x_1176_; lean_object* v___x_1177_; 
v___x_1174_ = lean_array_mk(v_ctors_1144_);
v_sz_1175_ = lean_array_size(v___x_1174_);
v___x_1176_ = ((size_t)0ULL);
v___x_1177_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5(v_sz_1175_, v___x_1176_, v___x_1174_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_);
if (lean_obj_tag(v___x_1177_) == 0)
{
lean_object* v_a_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1202_; 
v_a_1178_ = lean_ctor_get(v___x_1177_, 0);
v_isSharedCheck_1202_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1180_ = v___x_1177_;
v_isShared_1181_ = v_isSharedCheck_1202_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_a_1178_);
lean_dec(v___x_1177_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1202_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v_start_1182_; lean_object* v_stop_1183_; lean_object* v_start_1184_; lean_object* v_stop_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1197_; 
v_start_1182_ = lean_ctor_get(v_params_1163_, 1);
lean_inc(v_start_1182_);
v_stop_1183_ = lean_ctor_get(v_params_1163_, 2);
lean_inc(v_stop_1183_);
v_start_1184_ = lean_ctor_get(v_discrs_1166_, 1);
lean_inc(v_start_1184_);
v_stop_1185_ = lean_ctor_get(v_discrs_1166_, 2);
lean_inc(v_stop_1185_);
v___x_1186_ = lean_nat_sub(v_stop_1183_, v_start_1182_);
lean_dec(v_start_1182_);
lean_dec(v_stop_1183_);
v___x_1187_ = lean_nat_sub(v_stop_1185_, v_start_1184_);
lean_dec(v_start_1184_);
lean_dec(v_stop_1185_);
v___x_1188_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__2, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__2_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__2);
v___x_1189_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1186_);
lean_ctor_set(v___x_1189_, 1, v___x_1187_);
lean_ctor_set(v___x_1189_, 2, v_a_1178_);
lean_ctor_set(v___x_1189_, 3, v___y_1173_);
lean_ctor_set(v___x_1189_, 4, v_discrInfos_1169_);
lean_ctor_set(v___x_1189_, 5, v___x_1188_);
v___x_1190_ = lean_array_mk(v_us_1079_);
v___x_1191_ = l_Subarray_copy___redArg(v_params_1163_);
v___x_1192_ = l_Subarray_copy___redArg(v_discrs_1166_);
v___x_1193_ = l_Subarray_copy___redArg(v_alts_1170_);
v___x_1194_ = l_Subarray_copy___redArg(v___y_1172_);
v___x_1195_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1189_);
lean_ctor_set(v___x_1195_, 1, v_declName_1078_);
lean_ctor_set(v___x_1195_, 2, v___x_1190_);
lean_ctor_set(v___x_1195_, 3, v___x_1191_);
lean_ctor_set(v___x_1195_, 4, v_motive_1165_);
lean_ctor_set(v___x_1195_, 5, v___x_1192_);
lean_ctor_set(v___x_1195_, 6, v___x_1193_);
lean_ctor_set(v___x_1195_, 7, v___x_1194_);
if (v_isShared_1140_ == 0)
{
lean_ctor_set_tag(v___x_1139_, 1);
lean_ctor_set(v___x_1139_, 0, v___x_1195_);
v___x_1197_ = v___x_1139_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v___x_1195_);
v___x_1197_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
lean_object* v___x_1199_; 
if (v_isShared_1181_ == 0)
{
lean_ctor_set(v___x_1180_, 0, v___x_1197_);
v___x_1199_ = v___x_1180_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v___x_1197_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
}
}
else
{
lean_object* v_a_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1210_; 
lean_dec(v___y_1173_);
lean_dec_ref(v___y_1172_);
lean_dec_ref(v_alts_1170_);
lean_dec_ref(v_discrInfos_1169_);
lean_dec_ref(v_discrs_1166_);
lean_dec(v_motive_1165_);
lean_dec_ref(v_params_1163_);
lean_del_object(v___x_1139_);
lean_dec(v_us_1079_);
lean_dec(v_declName_1078_);
v_a_1203_ = lean_ctor_get(v___x_1177_, 0);
v_isSharedCheck_1210_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1205_ = v___x_1177_;
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_a_1203_);
lean_dec(v___x_1177_);
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
v___jp_1211_:
{
lean_object* v_levelParams_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; uint8_t v___x_1218_; 
v_levelParams_1214_ = lean_ctor_get(v_toConstantVal_1141_, 1);
lean_inc(v_levelParams_1214_);
lean_dec_ref(v_toConstantVal_1141_);
v___x_1215_ = l_Array_toSubarray___redArg(v_args_1150_, v_lower_1212_, v_upper_1213_);
v___x_1216_ = l_List_lengthTR___redArg(v_levelParams_1214_);
lean_dec(v_levelParams_1214_);
v___x_1217_ = l_List_lengthTR___redArg(v_us_1079_);
v___x_1218_ = lean_nat_dec_eq(v___x_1216_, v___x_1217_);
lean_dec(v___x_1217_);
lean_dec(v___x_1216_);
if (v___x_1218_ == 0)
{
lean_object* v___x_1219_; 
v___x_1219_ = ((lean_object*)(l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__3));
v___y_1172_ = v___x_1215_;
v___y_1173_ = v___x_1219_;
goto v___jp_1171_;
}
else
{
v___y_1172_ = v___x_1215_;
v___y_1173_ = v___x_1168_;
goto v___jp_1171_;
}
}
}
}
}
else
{
lean_object* v___x_1222_; lean_object* v___x_1224_; 
lean_dec(v_a_1133_);
lean_dec(v_us_1079_);
lean_dec(v_declName_1078_);
lean_dec_ref(v_e_1061_);
v___x_1222_ = lean_box(0);
if (v_isShared_1136_ == 0)
{
lean_ctor_set(v___x_1135_, 0, v___x_1222_);
v___x_1224_ = v___x_1135_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v___x_1222_);
v___x_1224_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
return v___x_1224_;
}
}
}
}
else
{
lean_object* v_a_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1234_; 
lean_dec(v_us_1079_);
lean_dec(v_declName_1078_);
lean_dec_ref(v_e_1061_);
v_a_1227_ = lean_ctor_get(v___x_1132_, 0);
v_isSharedCheck_1234_ = !lean_is_exclusive(v___x_1132_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_1229_ = v___x_1132_;
v_isShared_1230_ = v_isSharedCheck_1234_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_a_1227_);
lean_dec(v___x_1132_);
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
}
}
else
{
lean_dec_ref(v___x_1077_);
lean_dec_ref(v_e_1061_);
goto v___jp_1071_;
}
}
v___jp_1071_:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1072_ = lean_box(0);
v___x_1073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1072_);
return v___x_1073_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___boxed(lean_object* v_e_1236_, lean_object* v_alsoCasesOn_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_){
_start:
{
uint8_t v_alsoCasesOn_boxed_1246_; lean_object* v_res_1247_; 
v_alsoCasesOn_boxed_1246_ = lean_unbox(v_alsoCasesOn_1237_);
v_res_1247_ = l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2(v_e_1236_, v_alsoCasesOn_boxed_1246_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_);
lean_dec(v___y_1244_);
lean_dec_ref(v___y_1243_);
lean_dec(v___y_1242_);
lean_dec_ref(v___y_1241_);
lean_dec(v___y_1240_);
lean_dec_ref(v___y_1239_);
lean_dec(v___y_1238_);
return v_res_1247_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__5(size_t v_sz_1248_, size_t v_i_1249_, lean_object* v_bs_1250_){
_start:
{
uint8_t v___x_1251_; 
v___x_1251_ = lean_usize_dec_lt(v_i_1249_, v_sz_1248_);
if (v___x_1251_ == 0)
{
return v_bs_1250_;
}
else
{
lean_object* v_v_1252_; lean_object* v___x_1253_; lean_object* v_bs_x27_1254_; lean_object* v___y_1256_; lean_object* v___x_1261_; 
v_v_1252_ = lean_array_uget(v_bs_1250_, v_i_1249_);
v___x_1253_ = lean_unsigned_to_nat(0u);
v_bs_x27_1254_ = lean_array_uset(v_bs_1250_, v_i_1249_, v___x_1253_);
v___x_1261_ = l_Lean_Elab_WF_isWfParam_x3f(v_v_1252_);
if (lean_obj_tag(v___x_1261_) == 0)
{
v___y_1256_ = v_v_1252_;
goto v___jp_1255_;
}
else
{
lean_object* v_val_1262_; 
lean_dec(v_v_1252_);
v_val_1262_ = lean_ctor_get(v___x_1261_, 0);
lean_inc(v_val_1262_);
lean_dec_ref(v___x_1261_);
v___y_1256_ = v_val_1262_;
goto v___jp_1255_;
}
v___jp_1255_:
{
size_t v___x_1257_; size_t v___x_1258_; lean_object* v___x_1259_; 
v___x_1257_ = ((size_t)1ULL);
v___x_1258_ = lean_usize_add(v_i_1249_, v___x_1257_);
v___x_1259_ = lean_array_uset(v_bs_x27_1254_, v_i_1249_, v___y_1256_);
v_i_1249_ = v___x_1258_;
v_bs_1250_ = v___x_1259_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__5___boxed(lean_object* v_sz_1263_, lean_object* v_i_1264_, lean_object* v_bs_1265_){
_start:
{
size_t v_sz_boxed_1266_; size_t v_i_boxed_1267_; lean_object* v_res_1268_; 
v_sz_boxed_1266_ = lean_unbox_usize(v_sz_1263_);
lean_dec(v_sz_1263_);
v_i_boxed_1267_ = lean_unbox_usize(v_i_1264_);
lean_dec(v_i_1264_);
v_res_1268_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__5(v_sz_boxed_1266_, v_i_boxed_1267_, v_bs_1265_);
return v_res_1268_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_WF_paramMatcher_spec__3(lean_object* v_as_1269_, size_t v_i_1270_, size_t v_stop_1271_){
_start:
{
uint8_t v___x_1272_; 
v___x_1272_ = lean_usize_dec_eq(v_i_1270_, v_stop_1271_);
if (v___x_1272_ == 0)
{
uint8_t v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1273_ = 1;
v___x_1274_ = lean_array_uget_borrowed(v_as_1269_, v_i_1270_);
v___x_1275_ = l_Lean_Elab_WF_isWfParam_x3f(v___x_1274_);
if (lean_obj_tag(v___x_1275_) == 0)
{
if (v___x_1272_ == 0)
{
size_t v___x_1276_; size_t v___x_1277_; 
v___x_1276_ = ((size_t)1ULL);
v___x_1277_ = lean_usize_add(v_i_1270_, v___x_1276_);
v_i_1270_ = v___x_1277_;
goto _start;
}
else
{
return v___x_1273_;
}
}
else
{
lean_dec_ref(v___x_1275_);
return v___x_1273_;
}
}
else
{
uint8_t v___x_1279_; 
v___x_1279_ = 0;
return v___x_1279_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_WF_paramMatcher_spec__3___boxed(lean_object* v_as_1280_, lean_object* v_i_1281_, lean_object* v_stop_1282_){
_start:
{
size_t v_i_boxed_1283_; size_t v_stop_boxed_1284_; uint8_t v_res_1285_; lean_object* v_r_1286_; 
v_i_boxed_1283_ = lean_unbox_usize(v_i_1281_);
lean_dec(v_i_1281_);
v_stop_boxed_1284_ = lean_unbox_usize(v_stop_1282_);
lean_dec(v_stop_1282_);
v_res_1285_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_WF_paramMatcher_spec__3(v_as_1280_, v_i_boxed_1283_, v_stop_boxed_1284_);
lean_dec_ref(v_as_1280_);
v_r_1286_ = lean_box(v_res_1285_);
return v_r_1286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramMatcher(lean_object* v_e_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_){
_start:
{
uint8_t v___x_1296_; lean_object* v___x_1297_; 
v___x_1296_ = 1;
v___x_1297_ = l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2(v_e_1287_, v___x_1296_, v_a_1288_, v_a_1289_, v_a_1290_, v_a_1291_, v_a_1292_, v_a_1293_, v_a_1294_);
if (lean_obj_tag(v___x_1297_) == 0)
{
lean_object* v_a_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1360_; 
v_a_1298_ = lean_ctor_get(v___x_1297_, 0);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1297_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1300_ = v___x_1297_;
v_isShared_1301_ = v_isSharedCheck_1360_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_a_1298_);
lean_dec(v___x_1297_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1360_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
if (lean_obj_tag(v_a_1298_) == 1)
{
lean_object* v_val_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1357_; 
v_val_1307_ = lean_ctor_get(v_a_1298_, 0);
v_isSharedCheck_1357_ = !lean_is_exclusive(v_a_1298_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1309_ = v_a_1298_;
v_isShared_1310_ = v_isSharedCheck_1357_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_val_1307_);
lean_dec(v_a_1298_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1357_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v_toMatcherInfo_1311_; lean_object* v_matcherName_1312_; lean_object* v_matcherLevels_1313_; lean_object* v_params_1314_; lean_object* v_motive_1315_; lean_object* v_discrs_1316_; lean_object* v_alts_1317_; lean_object* v_remaining_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1356_; 
v_toMatcherInfo_1311_ = lean_ctor_get(v_val_1307_, 0);
v_matcherName_1312_ = lean_ctor_get(v_val_1307_, 1);
v_matcherLevels_1313_ = lean_ctor_get(v_val_1307_, 2);
v_params_1314_ = lean_ctor_get(v_val_1307_, 3);
v_motive_1315_ = lean_ctor_get(v_val_1307_, 4);
v_discrs_1316_ = lean_ctor_get(v_val_1307_, 5);
v_alts_1317_ = lean_ctor_get(v_val_1307_, 6);
v_remaining_1318_ = lean_ctor_get(v_val_1307_, 7);
v_isSharedCheck_1356_ = !lean_is_exclusive(v_val_1307_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1320_ = v_val_1307_;
v_isShared_1321_ = v_isSharedCheck_1356_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_remaining_1318_);
lean_inc(v_alts_1317_);
lean_inc(v_discrs_1316_);
lean_inc(v_motive_1315_);
lean_inc(v_params_1314_);
lean_inc(v_matcherLevels_1313_);
lean_inc(v_matcherName_1312_);
lean_inc(v_toMatcherInfo_1311_);
lean_dec(v_val_1307_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1356_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v___x_1322_; lean_object* v___x_1323_; uint8_t v___x_1324_; 
v___x_1322_ = lean_unsigned_to_nat(0u);
v___x_1323_ = lean_array_get_size(v_discrs_1316_);
v___x_1324_ = lean_nat_dec_lt(v___x_1322_, v___x_1323_);
if (v___x_1324_ == 0)
{
lean_del_object(v___x_1320_);
lean_dec_ref(v_remaining_1318_);
lean_dec_ref(v_alts_1317_);
lean_dec_ref(v_discrs_1316_);
lean_dec_ref(v_motive_1315_);
lean_dec_ref(v_params_1314_);
lean_dec_ref(v_matcherLevels_1313_);
lean_dec(v_matcherName_1312_);
lean_dec_ref(v_toMatcherInfo_1311_);
lean_del_object(v___x_1309_);
goto v___jp_1302_;
}
else
{
if (v___x_1324_ == 0)
{
lean_del_object(v___x_1320_);
lean_dec_ref(v_remaining_1318_);
lean_dec_ref(v_alts_1317_);
lean_dec_ref(v_discrs_1316_);
lean_dec_ref(v_motive_1315_);
lean_dec_ref(v_params_1314_);
lean_dec_ref(v_matcherLevels_1313_);
lean_dec(v_matcherName_1312_);
lean_dec_ref(v_toMatcherInfo_1311_);
lean_del_object(v___x_1309_);
goto v___jp_1302_;
}
else
{
size_t v___x_1325_; size_t v___x_1326_; uint8_t v___x_1327_; 
v___x_1325_ = ((size_t)0ULL);
v___x_1326_ = lean_usize_of_nat(v___x_1323_);
v___x_1327_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_WF_paramMatcher_spec__3(v_discrs_1316_, v___x_1325_, v___x_1326_);
if (v___x_1327_ == 0)
{
lean_del_object(v___x_1320_);
lean_dec_ref(v_remaining_1318_);
lean_dec_ref(v_alts_1317_);
lean_dec_ref(v_discrs_1316_);
lean_dec_ref(v_motive_1315_);
lean_dec_ref(v_params_1314_);
lean_dec_ref(v_matcherLevels_1313_);
lean_dec(v_matcherName_1312_);
lean_dec_ref(v_toMatcherInfo_1311_);
lean_del_object(v___x_1309_);
goto v___jp_1302_;
}
else
{
size_t v_sz_1328_; lean_object* v___x_1329_; 
lean_del_object(v___x_1300_);
v_sz_1328_ = lean_array_size(v_alts_1317_);
v___x_1329_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__4(v_sz_1328_, v___x_1325_, v_alts_1317_, v_a_1288_, v_a_1289_, v_a_1290_, v_a_1291_, v_a_1292_, v_a_1293_, v_a_1294_);
if (lean_obj_tag(v___x_1329_) == 0)
{
lean_object* v_a_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1347_; 
v_a_1330_ = lean_ctor_get(v___x_1329_, 0);
v_isSharedCheck_1347_ = !lean_is_exclusive(v___x_1329_);
if (v_isSharedCheck_1347_ == 0)
{
v___x_1332_ = v___x_1329_;
v_isShared_1333_ = v_isSharedCheck_1347_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_a_1330_);
lean_dec(v___x_1329_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1347_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
size_t v_sz_1334_; lean_object* v___x_1335_; lean_object* v___x_1337_; 
v_sz_1334_ = lean_array_size(v_discrs_1316_);
v___x_1335_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__5(v_sz_1334_, v___x_1325_, v_discrs_1316_);
if (v_isShared_1321_ == 0)
{
lean_ctor_set(v___x_1320_, 6, v_a_1330_);
lean_ctor_set(v___x_1320_, 5, v___x_1335_);
v___x_1337_ = v___x_1320_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v_toMatcherInfo_1311_);
lean_ctor_set(v_reuseFailAlloc_1346_, 1, v_matcherName_1312_);
lean_ctor_set(v_reuseFailAlloc_1346_, 2, v_matcherLevels_1313_);
lean_ctor_set(v_reuseFailAlloc_1346_, 3, v_params_1314_);
lean_ctor_set(v_reuseFailAlloc_1346_, 4, v_motive_1315_);
lean_ctor_set(v_reuseFailAlloc_1346_, 5, v___x_1335_);
lean_ctor_set(v_reuseFailAlloc_1346_, 6, v_a_1330_);
lean_ctor_set(v_reuseFailAlloc_1346_, 7, v_remaining_1318_);
v___x_1337_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
lean_object* v___x_1338_; lean_object* v___x_1340_; 
v___x_1338_ = l_Lean_Meta_MatcherApp_toExpr(v___x_1337_);
if (v_isShared_1310_ == 0)
{
lean_ctor_set(v___x_1309_, 0, v___x_1338_);
v___x_1340_ = v___x_1309_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v___x_1338_);
v___x_1340_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
lean_object* v___x_1341_; lean_object* v___x_1343_; 
v___x_1341_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1341_, 0, v___x_1340_);
if (v_isShared_1333_ == 0)
{
lean_ctor_set(v___x_1332_, 0, v___x_1341_);
v___x_1343_ = v___x_1332_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v___x_1341_);
v___x_1343_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
return v___x_1343_;
}
}
}
}
}
else
{
lean_object* v_a_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1355_; 
lean_del_object(v___x_1320_);
lean_dec_ref(v_remaining_1318_);
lean_dec_ref(v_discrs_1316_);
lean_dec_ref(v_motive_1315_);
lean_dec_ref(v_params_1314_);
lean_dec_ref(v_matcherLevels_1313_);
lean_dec(v_matcherName_1312_);
lean_dec_ref(v_toMatcherInfo_1311_);
lean_del_object(v___x_1309_);
v_a_1348_ = lean_ctor_get(v___x_1329_, 0);
v_isSharedCheck_1355_ = !lean_is_exclusive(v___x_1329_);
if (v_isSharedCheck_1355_ == 0)
{
v___x_1350_ = v___x_1329_;
v_isShared_1351_ = v_isSharedCheck_1355_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_a_1348_);
lean_dec(v___x_1329_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1355_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
lean_object* v___x_1353_; 
if (v_isShared_1351_ == 0)
{
v___x_1353_ = v___x_1350_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v_a_1348_);
v___x_1353_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
return v___x_1353_;
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
lean_object* v___x_1358_; lean_object* v___x_1359_; 
lean_del_object(v___x_1300_);
lean_dec(v_a_1298_);
v___x_1358_ = ((lean_object*)(l_Lean_Elab_WF_paramProj___closed__0));
v___x_1359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1359_, 0, v___x_1358_);
return v___x_1359_;
}
v___jp_1302_:
{
lean_object* v___x_1303_; lean_object* v___x_1305_; 
v___x_1303_ = ((lean_object*)(l_Lean_Elab_WF_paramProj___closed__0));
if (v_isShared_1301_ == 0)
{
lean_ctor_set(v___x_1300_, 0, v___x_1303_);
v___x_1305_ = v___x_1300_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v___x_1303_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
return v___x_1305_;
}
}
}
}
else
{
lean_object* v_a_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1368_; 
v_a_1361_ = lean_ctor_get(v___x_1297_, 0);
v_isSharedCheck_1368_ = !lean_is_exclusive(v___x_1297_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1363_ = v___x_1297_;
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_a_1361_);
lean_dec(v___x_1297_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1366_; 
if (v_isShared_1364_ == 0)
{
v___x_1366_ = v___x_1363_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_a_1361_);
v___x_1366_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
return v___x_1366_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramMatcher___boxed(lean_object* v_e_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_){
_start:
{
lean_object* v_res_1378_; 
v_res_1378_ = l_Lean_Elab_WF_paramMatcher(v_e_1369_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_);
lean_dec(v_a_1376_);
lean_dec_ref(v_a_1375_);
lean_dec(v_a_1374_);
lean_dec_ref(v_a_1373_);
lean_dec(v_a_1372_);
lean_dec_ref(v_a_1371_);
lean_dec(v_a_1370_);
return v_res_1378_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__0(size_t v_sz_1379_, size_t v_i_1380_, lean_object* v_bs_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_){
_start:
{
lean_object* v___x_1390_; 
v___x_1390_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__0___redArg(v_sz_1379_, v_i_1380_, v_bs_1381_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_);
return v___x_1390_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__0___boxed(lean_object* v_sz_1391_, lean_object* v_i_1392_, lean_object* v_bs_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_){
_start:
{
size_t v_sz_boxed_1402_; size_t v_i_boxed_1403_; lean_object* v_res_1404_; 
v_sz_boxed_1402_ = lean_unbox_usize(v_sz_1391_);
lean_dec(v_sz_1391_);
v_i_boxed_1403_ = lean_unbox_usize(v_i_1392_);
lean_dec(v_i_1392_);
v_res_1404_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__0(v_sz_boxed_1402_, v_i_boxed_1403_, v_bs_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_);
lean_dec(v___y_1400_);
lean_dec_ref(v___y_1399_);
lean_dec(v___y_1398_);
lean_dec_ref(v___y_1397_);
lean_dec(v___y_1396_);
lean_dec_ref(v___y_1395_);
lean_dec(v___y_1394_);
return v_res_1404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__4(lean_object* v_declName_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_){
_start:
{
lean_object* v___x_1414_; 
v___x_1414_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__4___redArg(v_declName_1405_, v___y_1412_);
return v___x_1414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__4___boxed(lean_object* v_declName_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_){
_start:
{
lean_object* v_res_1424_; 
v_res_1424_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__4(v_declName_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
lean_dec(v___y_1420_);
lean_dec_ref(v___y_1419_);
lean_dec(v___y_1418_);
lean_dec_ref(v___y_1417_);
lean_dec(v___y_1416_);
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3(lean_object* v_00_u03b1_1425_, lean_object* v_constName_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_){
_start:
{
lean_object* v___x_1435_; 
v___x_1435_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3___redArg(v_constName_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_);
return v___x_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1436_, lean_object* v_constName_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_){
_start:
{
lean_object* v_res_1446_; 
v_res_1446_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3(v_00_u03b1_1436_, v_constName_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_);
lean_dec(v___y_1444_);
lean_dec_ref(v___y_1443_);
lean_dec(v___y_1442_);
lean_dec_ref(v___y_1441_);
lean_dec(v___y_1440_);
lean_dec_ref(v___y_1439_);
lean_dec(v___y_1438_);
return v_res_1446_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9(lean_object* v_00_u03b1_1447_, lean_object* v_ref_1448_, lean_object* v_constName_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_){
_start:
{
lean_object* v___x_1458_; 
v___x_1458_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg(v_ref_1448_, v_constName_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_);
return v___x_1458_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___boxed(lean_object* v_00_u03b1_1459_, lean_object* v_ref_1460_, lean_object* v_constName_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_){
_start:
{
lean_object* v_res_1470_; 
v_res_1470_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9(v_00_u03b1_1459_, v_ref_1460_, v_constName_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_);
lean_dec(v___y_1468_);
lean_dec_ref(v___y_1467_);
lean_dec(v___y_1466_);
lean_dec_ref(v___y_1465_);
lean_dec(v___y_1464_);
lean_dec_ref(v___y_1463_);
lean_dec(v___y_1462_);
lean_dec(v_ref_1460_);
return v_res_1470_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11(lean_object* v_00_u03b1_1471_, lean_object* v_ref_1472_, lean_object* v_msg_1473_, lean_object* v_declHint_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_){
_start:
{
lean_object* v___x_1483_; 
v___x_1483_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11___redArg(v_ref_1472_, v_msg_1473_, v_declHint_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_);
return v___x_1483_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11___boxed(lean_object* v_00_u03b1_1484_, lean_object* v_ref_1485_, lean_object* v_msg_1486_, lean_object* v_declHint_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_){
_start:
{
lean_object* v_res_1496_; 
v_res_1496_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11(v_00_u03b1_1484_, v_ref_1485_, v_msg_1486_, v_declHint_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_);
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
lean_dec(v___y_1492_);
lean_dec_ref(v___y_1491_);
lean_dec(v___y_1490_);
lean_dec_ref(v___y_1489_);
lean_dec(v___y_1488_);
lean_dec(v_ref_1485_);
return v_res_1496_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13(lean_object* v_msg_1497_, lean_object* v_declHint_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_){
_start:
{
lean_object* v___x_1507_; 
v___x_1507_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg(v_msg_1497_, v_declHint_1498_, v___y_1505_);
return v___x_1507_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___boxed(lean_object* v_msg_1508_, lean_object* v_declHint_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_){
_start:
{
lean_object* v_res_1518_; 
v_res_1518_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13(v_msg_1508_, v_declHint_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_);
lean_dec(v___y_1516_);
lean_dec_ref(v___y_1515_);
lean_dec(v___y_1514_);
lean_dec_ref(v___y_1513_);
lean_dec(v___y_1512_);
lean_dec_ref(v___y_1511_);
lean_dec(v___y_1510_);
return v_res_1518_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13(lean_object* v_00_u03b1_1519_, lean_object* v_ref_1520_, lean_object* v_msg_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_){
_start:
{
lean_object* v___x_1530_; 
v___x_1530_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13___redArg(v_ref_1520_, v_msg_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_);
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13___boxed(lean_object* v_00_u03b1_1531_, lean_object* v_ref_1532_, lean_object* v_msg_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_){
_start:
{
lean_object* v_res_1542_; 
v_res_1542_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13(v_00_u03b1_1531_, v_ref_1532_, v_msg_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_);
lean_dec(v___y_1540_);
lean_dec_ref(v___y_1539_);
lean_dec(v___y_1538_);
lean_dec_ref(v___y_1537_);
lean_dec(v___y_1536_);
lean_dec_ref(v___y_1535_);
lean_dec(v___y_1534_);
lean_dec(v_ref_1532_);
return v_res_1542_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15(lean_object* v_00_u03b1_1543_, lean_object* v_msg_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_){
_start:
{
lean_object* v___x_1553_; 
v___x_1553_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15___redArg(v_msg_1544_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
return v___x_1553_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15___boxed(lean_object* v_00_u03b1_1554_, lean_object* v_msg_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_){
_start:
{
lean_object* v_res_1564_; 
v_res_1564_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15(v_00_u03b1_1554_, v_msg_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_);
lean_dec(v___y_1562_);
lean_dec_ref(v___y_1561_);
lean_dec(v___y_1560_);
lean_dec_ref(v___y_1559_);
lean_dec(v___y_1558_);
lean_dec_ref(v___y_1557_);
lean_dec(v___y_1556_);
return v_res_1564_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__31_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_12_(){
_start:
{
lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; 
v___x_1572_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__31___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_12_));
v___x_1573_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__26___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_12_));
v___x_1574_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_paramMatcher___boxed), 9, 0);
v___x_1575_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1572_, v___x_1573_, v___x_1574_);
return v___x_1575_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__31_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_12____boxed(lean_object* v_a_1576_){
_start:
{
lean_object* v_res_1577_; 
v_res_1577_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__31_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_12_();
return v_res_1577_;
}
}
static lean_object* _init_l_Lean_Elab_WF_paramMatcher___regBuiltin_Lean_Elab_WF_paramMatcher_declare__1___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_14_(void){
_start:
{
lean_object* v___x_1578_; lean_object* v___x_1579_; 
v___x_1578_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_paramMatcher___boxed), 9, 0);
v___x_1579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1579_, 0, v___x_1578_);
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramMatcher___regBuiltin_Lean_Elab_WF_paramMatcher_declare__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_14_(){
_start:
{
lean_object* v___x_1581_; uint8_t v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; 
v___x_1581_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__31___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_12_));
v___x_1582_ = 1;
v___x_1583_ = lean_obj_once(&l_Lean_Elab_WF_paramMatcher___regBuiltin_Lean_Elab_WF_paramMatcher_declare__1___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_14_, &l_Lean_Elab_WF_paramMatcher___regBuiltin_Lean_Elab_WF_paramMatcher_declare__1___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_14__once, _init_l_Lean_Elab_WF_paramMatcher___regBuiltin_Lean_Elab_WF_paramMatcher_declare__1___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_14_);
v___x_1584_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1581_, v___x_1582_, v___x_1583_);
return v___x_1584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramMatcher___regBuiltin_Lean_Elab_WF_paramMatcher_declare__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_14____boxed(lean_object* v_a_1585_){
_start:
{
lean_object* v_res_1586_; 
v_res_1586_ = l_Lean_Elab_WF_paramMatcher___regBuiltin_Lean_Elab_WF_paramMatcher_declare__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_14_();
return v_res_1586_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_anyLetValueIsWfParam(lean_object* v_e_1587_){
_start:
{
if (lean_obj_tag(v_e_1587_) == 8)
{
lean_object* v_value_1588_; lean_object* v_body_1589_; lean_object* v___x_1590_; 
v_value_1588_ = lean_ctor_get(v_e_1587_, 2);
v_body_1589_ = lean_ctor_get(v_e_1587_, 3);
v___x_1590_ = l_Lean_Elab_WF_isWfParam_x3f(v_value_1588_);
if (lean_obj_tag(v___x_1590_) == 0)
{
v_e_1587_ = v_body_1589_;
goto _start;
}
else
{
uint8_t v___x_1592_; 
lean_dec_ref(v___x_1590_);
v___x_1592_ = 1;
return v___x_1592_;
}
}
else
{
uint8_t v___x_1593_; 
v___x_1593_ = 0;
return v___x_1593_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_anyLetValueIsWfParam___boxed(lean_object* v_e_1594_){
_start:
{
uint8_t v_res_1595_; lean_object* v_r_1596_; 
v_res_1595_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_anyLetValueIsWfParam(v_e_1594_);
lean_dec_ref(v_e_1594_);
v_r_1596_ = lean_box(v_res_1595_);
return v_r_1596_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_numLetsWithValueNotIsWfParam(lean_object* v_e_1597_, lean_object* v_acc_1598_){
_start:
{
if (lean_obj_tag(v_e_1597_) == 8)
{
lean_object* v_value_1599_; lean_object* v_body_1600_; lean_object* v___x_1601_; 
v_value_1599_ = lean_ctor_get(v_e_1597_, 2);
v_body_1600_ = lean_ctor_get(v_e_1597_, 3);
v___x_1601_ = l_Lean_Elab_WF_isWfParam_x3f(v_value_1599_);
if (lean_obj_tag(v___x_1601_) == 0)
{
lean_object* v___x_1602_; lean_object* v___x_1603_; 
v___x_1602_ = lean_unsigned_to_nat(1u);
v___x_1603_ = lean_nat_add(v_acc_1598_, v___x_1602_);
lean_dec(v_acc_1598_);
v_e_1597_ = v_body_1600_;
v_acc_1598_ = v___x_1603_;
goto _start;
}
else
{
lean_dec_ref(v___x_1601_);
return v_acc_1598_;
}
}
else
{
return v_acc_1598_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_numLetsWithValueNotIsWfParam___boxed(lean_object* v_e_1605_, lean_object* v_acc_1606_){
_start:
{
lean_object* v_res_1607_; 
v_res_1607_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_numLetsWithValueNotIsWfParam(v_e_1605_, v_acc_1606_);
lean_dec_ref(v_e_1605_);
return v_res_1607_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__0(lean_object* v_msg_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_){
_start:
{
lean_object* v___f_1615_; lean_object* v___x_1300__overap_1616_; lean_object* v___x_1617_; 
v___f_1615_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__0___closed__0));
v___x_1300__overap_1616_ = lean_panic_fn(v___f_1615_, v_msg_1609_);
lean_inc(v___y_1613_);
lean_inc_ref(v___y_1612_);
lean_inc(v___y_1611_);
lean_inc_ref(v___y_1610_);
v___x_1617_ = lean_apply_5(v___x_1300__overap_1616_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, lean_box(0));
return v___x_1617_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__0___boxed(lean_object* v_msg_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_){
_start:
{
lean_object* v_res_1624_; 
v_res_1624_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__0(v_msg_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_);
lean_dec(v___y_1622_);
lean_dec_ref(v___y_1621_);
lean_dec(v___y_1620_);
lean_dec_ref(v___y_1619_);
return v_res_1624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg___lam__0(lean_object* v_k_1625_, lean_object* v_b_1626_, lean_object* v_c_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_){
_start:
{
lean_object* v___x_1633_; 
lean_inc(v___y_1631_);
lean_inc_ref(v___y_1630_);
lean_inc(v___y_1629_);
lean_inc_ref(v___y_1628_);
v___x_1633_ = lean_apply_7(v_k_1625_, v_b_1626_, v_c_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, lean_box(0));
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg___lam__0___boxed(lean_object* v_k_1634_, lean_object* v_b_1635_, lean_object* v_c_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_){
_start:
{
lean_object* v_res_1642_; 
v_res_1642_ = l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg___lam__0(v_k_1634_, v_b_1635_, v_c_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_);
lean_dec(v___y_1640_);
lean_dec_ref(v___y_1639_);
lean_dec(v___y_1638_);
lean_dec_ref(v___y_1637_);
return v_res_1642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg(lean_object* v_e_1643_, lean_object* v_maxFVars_x3f_1644_, lean_object* v_k_1645_, uint8_t v_cleanupAnnotations_1646_, uint8_t v_preserveNondepLet_1647_, uint8_t v_nondepLetOnly_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_){
_start:
{
lean_object* v___f_1654_; uint8_t v___x_1655_; uint8_t v___x_1656_; lean_object* v___x_1657_; 
v___f_1654_ = lean_alloc_closure((void*)(l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1654_, 0, v_k_1645_);
v___x_1655_ = 0;
v___x_1656_ = 1;
v___x_1657_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_1643_, v___x_1655_, v___x_1656_, v_preserveNondepLet_1647_, v_nondepLetOnly_1648_, v_maxFVars_x3f_1644_, v___f_1654_, v_cleanupAnnotations_1646_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_);
if (lean_obj_tag(v___x_1657_) == 0)
{
lean_object* v_a_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1665_; 
v_a_1658_ = lean_ctor_get(v___x_1657_, 0);
v_isSharedCheck_1665_ = !lean_is_exclusive(v___x_1657_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1660_ = v___x_1657_;
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_a_1658_);
lean_dec(v___x_1657_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___x_1663_; 
if (v_isShared_1661_ == 0)
{
v___x_1663_ = v___x_1660_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v_a_1658_);
v___x_1663_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
return v___x_1663_;
}
}
}
else
{
lean_object* v_a_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1673_; 
v_a_1666_ = lean_ctor_get(v___x_1657_, 0);
v_isSharedCheck_1673_ = !lean_is_exclusive(v___x_1657_);
if (v_isSharedCheck_1673_ == 0)
{
v___x_1668_ = v___x_1657_;
v_isShared_1669_ = v_isSharedCheck_1673_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_a_1666_);
lean_dec(v___x_1657_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1673_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
lean_object* v___x_1671_; 
if (v_isShared_1669_ == 0)
{
v___x_1671_ = v___x_1668_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v_a_1666_);
v___x_1671_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
return v___x_1671_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg___boxed(lean_object* v_e_1674_, lean_object* v_maxFVars_x3f_1675_, lean_object* v_k_1676_, lean_object* v_cleanupAnnotations_1677_, lean_object* v_preserveNondepLet_1678_, lean_object* v_nondepLetOnly_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1685_; uint8_t v_preserveNondepLet_boxed_1686_; uint8_t v_nondepLetOnly_boxed_1687_; lean_object* v_res_1688_; 
v_cleanupAnnotations_boxed_1685_ = lean_unbox(v_cleanupAnnotations_1677_);
v_preserveNondepLet_boxed_1686_ = lean_unbox(v_preserveNondepLet_1678_);
v_nondepLetOnly_boxed_1687_ = lean_unbox(v_nondepLetOnly_1679_);
v_res_1688_ = l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg(v_e_1674_, v_maxFVars_x3f_1675_, v_k_1676_, v_cleanupAnnotations_boxed_1685_, v_preserveNondepLet_boxed_1686_, v_nondepLetOnly_boxed_1687_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
lean_dec(v_maxFVars_x3f_1675_);
return v_res_1688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1(lean_object* v_00_u03b1_1689_, lean_object* v_e_1690_, lean_object* v_maxFVars_x3f_1691_, lean_object* v_k_1692_, uint8_t v_cleanupAnnotations_1693_, uint8_t v_preserveNondepLet_1694_, uint8_t v_nondepLetOnly_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_){
_start:
{
lean_object* v___x_1701_; 
v___x_1701_ = l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg(v_e_1690_, v_maxFVars_x3f_1691_, v_k_1692_, v_cleanupAnnotations_1693_, v_preserveNondepLet_1694_, v_nondepLetOnly_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_);
return v___x_1701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___boxed(lean_object* v_00_u03b1_1702_, lean_object* v_e_1703_, lean_object* v_maxFVars_x3f_1704_, lean_object* v_k_1705_, lean_object* v_cleanupAnnotations_1706_, lean_object* v_preserveNondepLet_1707_, lean_object* v_nondepLetOnly_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1714_; uint8_t v_preserveNondepLet_boxed_1715_; uint8_t v_nondepLetOnly_boxed_1716_; lean_object* v_res_1717_; 
v_cleanupAnnotations_boxed_1714_ = lean_unbox(v_cleanupAnnotations_1706_);
v_preserveNondepLet_boxed_1715_ = lean_unbox(v_preserveNondepLet_1707_);
v_nondepLetOnly_boxed_1716_ = lean_unbox(v_nondepLetOnly_1708_);
v_res_1717_ = l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1(v_00_u03b1_1702_, v_e_1703_, v_maxFVars_x3f_1704_, v_k_1705_, v_cleanupAnnotations_boxed_1714_, v_preserveNondepLet_boxed_1715_, v_nondepLetOnly_boxed_1716_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_);
lean_dec(v___y_1712_);
lean_dec_ref(v___y_1711_);
lean_dec(v___y_1710_);
lean_dec_ref(v___y_1709_);
lean_dec(v_maxFVars_x3f_1704_);
return v_res_1717_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__0(void){
_start:
{
lean_object* v___x_1718_; lean_object* v___x_1719_; 
v___x_1718_ = lean_unsigned_to_nat(0u);
v___x_1719_ = l_Lean_Expr_bvar___override(v___x_1718_);
return v___x_1719_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__4(void){
_start:
{
lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; 
v___x_1723_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__3));
v___x_1724_ = lean_unsigned_to_nat(6u);
v___x_1725_ = lean_unsigned_to_nat(138u);
v___x_1726_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__2));
v___x_1727_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__1));
v___x_1728_ = l_mkPanicMessageWithDecl(v___x_1727_, v___x_1726_, v___x_1725_, v___x_1724_, v___x_1723_);
return v___x_1728_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___lam__0___boxed(lean_object* v_xs_1729_, lean_object* v_b_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_){
_start:
{
lean_object* v_res_1736_; 
v_res_1736_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___lam__0(v_xs_1729_, v_b_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_);
lean_dec(v___y_1734_);
lean_dec_ref(v___y_1733_);
lean_dec(v___y_1732_);
lean_dec_ref(v___y_1731_);
lean_dec_ref(v_xs_1729_);
return v_res_1736_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet(lean_object* v_e_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_){
_start:
{
if (lean_obj_tag(v_e_1737_) == 8)
{
lean_object* v_declName_1743_; lean_object* v_type_1744_; lean_object* v_value_1745_; lean_object* v_body_1746_; uint8_t v_nondep_1747_; lean_object* v___x_1748_; 
v_declName_1743_ = lean_ctor_get(v_e_1737_, 0);
v_type_1744_ = lean_ctor_get(v_e_1737_, 1);
v_value_1745_ = lean_ctor_get(v_e_1737_, 2);
v_body_1746_ = lean_ctor_get(v_e_1737_, 3);
v_nondep_1747_ = lean_ctor_get_uint8(v_e_1737_, sizeof(void*)*4 + 8);
v___x_1748_ = l_Lean_Elab_WF_isWfParam_x3f(v_value_1745_);
if (lean_obj_tag(v___x_1748_) == 1)
{
lean_object* v_val_1749_; lean_object* v___x_1750_; 
v_val_1749_ = lean_ctor_get(v___x_1748_, 0);
lean_inc(v_val_1749_);
lean_dec_ref(v___x_1748_);
lean_inc_ref(v_type_1744_);
v___x_1750_ = l_Lean_Meta_isProp(v_type_1744_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_);
if (lean_obj_tag(v___x_1750_) == 0)
{
lean_object* v_a_1751_; uint8_t v___y_1753_; uint8_t v___x_1761_; 
v_a_1751_ = lean_ctor_get(v___x_1750_, 0);
lean_inc(v_a_1751_);
lean_dec_ref(v___x_1750_);
v___x_1761_ = lean_unbox(v_a_1751_);
lean_dec(v_a_1751_);
if (v___x_1761_ == 0)
{
lean_object* v___x_1762_; 
lean_inc_ref(v_type_1744_);
v___x_1762_ = l_Lean_Meta_getLevel(v_type_1744_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_);
if (lean_obj_tag(v___x_1762_) == 0)
{
lean_object* v_a_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; uint8_t v___y_1772_; size_t v___x_1781_; uint8_t v___x_1782_; 
v_a_1763_ = lean_ctor_get(v___x_1762_, 0);
lean_inc(v_a_1763_);
lean_dec_ref(v___x_1762_);
v___x_1764_ = ((lean_object*)(l_Lean_Elab_WF_isWfParam_x3f___closed__1));
v___x_1765_ = lean_box(0);
v___x_1766_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1766_, 0, v_a_1763_);
lean_ctor_set(v___x_1766_, 1, v___x_1765_);
v___x_1767_ = l_Lean_Expr_const___override(v___x_1764_, v___x_1766_);
v___x_1768_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__0, &l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__0);
lean_inc_ref(v_type_1744_);
v___x_1769_ = l_Lean_mkAppB(v___x_1767_, v_type_1744_, v___x_1768_);
v___x_1770_ = lean_expr_instantiate1(v_body_1746_, v___x_1769_);
lean_dec_ref(v___x_1769_);
v___x_1781_ = lean_ptr_addr(v_type_1744_);
v___x_1782_ = lean_usize_dec_eq(v___x_1781_, v___x_1781_);
if (v___x_1782_ == 0)
{
v___y_1772_ = v___x_1782_;
goto v___jp_1771_;
}
else
{
size_t v___x_1783_; size_t v___x_1784_; uint8_t v___x_1785_; 
v___x_1783_ = lean_ptr_addr(v_value_1745_);
v___x_1784_ = lean_ptr_addr(v_val_1749_);
v___x_1785_ = lean_usize_dec_eq(v___x_1783_, v___x_1784_);
v___y_1772_ = v___x_1785_;
goto v___jp_1771_;
}
v___jp_1771_:
{
if (v___y_1772_ == 0)
{
lean_object* v___x_1773_; 
lean_inc_ref(v_type_1744_);
lean_inc(v_declName_1743_);
lean_dec_ref(v_e_1737_);
v___x_1773_ = l_Lean_Expr_letE___override(v_declName_1743_, v_type_1744_, v_val_1749_, v___x_1770_, v_nondep_1747_);
v_e_1737_ = v___x_1773_;
goto _start;
}
else
{
size_t v___x_1775_; size_t v___x_1776_; uint8_t v___x_1777_; 
v___x_1775_ = lean_ptr_addr(v_body_1746_);
v___x_1776_ = lean_ptr_addr(v___x_1770_);
v___x_1777_ = lean_usize_dec_eq(v___x_1775_, v___x_1776_);
if (v___x_1777_ == 0)
{
lean_object* v___x_1778_; 
lean_inc_ref(v_type_1744_);
lean_inc(v_declName_1743_);
lean_dec_ref(v_e_1737_);
v___x_1778_ = l_Lean_Expr_letE___override(v_declName_1743_, v_type_1744_, v_val_1749_, v___x_1770_, v_nondep_1747_);
v_e_1737_ = v___x_1778_;
goto _start;
}
else
{
lean_dec_ref(v___x_1770_);
lean_dec(v_val_1749_);
goto _start;
}
}
}
}
else
{
lean_object* v_a_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1793_; 
lean_dec(v_val_1749_);
lean_dec_ref(v_e_1737_);
v_a_1786_ = lean_ctor_get(v___x_1762_, 0);
v_isSharedCheck_1793_ = !lean_is_exclusive(v___x_1762_);
if (v_isSharedCheck_1793_ == 0)
{
v___x_1788_ = v___x_1762_;
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_a_1786_);
lean_dec(v___x_1762_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v___x_1791_; 
if (v_isShared_1789_ == 0)
{
v___x_1791_ = v___x_1788_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_a_1786_);
v___x_1791_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
return v___x_1791_;
}
}
}
}
else
{
size_t v___x_1794_; uint8_t v___x_1795_; 
v___x_1794_ = lean_ptr_addr(v_type_1744_);
v___x_1795_ = lean_usize_dec_eq(v___x_1794_, v___x_1794_);
if (v___x_1795_ == 0)
{
v___y_1753_ = v___x_1795_;
goto v___jp_1752_;
}
else
{
size_t v___x_1796_; size_t v___x_1797_; uint8_t v___x_1798_; 
v___x_1796_ = lean_ptr_addr(v_value_1745_);
v___x_1797_ = lean_ptr_addr(v_val_1749_);
v___x_1798_ = lean_usize_dec_eq(v___x_1796_, v___x_1797_);
v___y_1753_ = v___x_1798_;
goto v___jp_1752_;
}
}
v___jp_1752_:
{
if (v___y_1753_ == 0)
{
lean_object* v___x_1754_; 
lean_inc_ref(v_body_1746_);
lean_inc_ref(v_type_1744_);
lean_inc(v_declName_1743_);
lean_dec_ref(v_e_1737_);
v___x_1754_ = l_Lean_Expr_letE___override(v_declName_1743_, v_type_1744_, v_val_1749_, v_body_1746_, v_nondep_1747_);
v_e_1737_ = v___x_1754_;
goto _start;
}
else
{
size_t v___x_1756_; uint8_t v___x_1757_; 
v___x_1756_ = lean_ptr_addr(v_body_1746_);
v___x_1757_ = lean_usize_dec_eq(v___x_1756_, v___x_1756_);
if (v___x_1757_ == 0)
{
lean_object* v___x_1758_; 
lean_inc_ref(v_body_1746_);
lean_inc_ref(v_type_1744_);
lean_inc(v_declName_1743_);
lean_dec_ref(v_e_1737_);
v___x_1758_ = l_Lean_Expr_letE___override(v_declName_1743_, v_type_1744_, v_val_1749_, v_body_1746_, v_nondep_1747_);
v_e_1737_ = v___x_1758_;
goto _start;
}
else
{
lean_dec(v_val_1749_);
goto _start;
}
}
}
}
else
{
lean_object* v_a_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1806_; 
lean_dec(v_val_1749_);
lean_dec_ref(v_e_1737_);
v_a_1799_ = lean_ctor_get(v___x_1750_, 0);
v_isSharedCheck_1806_ = !lean_is_exclusive(v___x_1750_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1801_ = v___x_1750_;
v_isShared_1802_ = v_isSharedCheck_1806_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_a_1799_);
lean_dec(v___x_1750_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1806_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v___x_1804_; 
if (v_isShared_1802_ == 0)
{
v___x_1804_ = v___x_1801_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v_a_1799_);
v___x_1804_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
return v___x_1804_;
}
}
}
}
else
{
lean_object* v___x_1807_; lean_object* v_num_1808_; uint8_t v___x_1809_; 
lean_dec(v___x_1748_);
v___x_1807_ = lean_unsigned_to_nat(0u);
v_num_1808_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_numLetsWithValueNotIsWfParam(v_e_1737_, v___x_1807_);
v___x_1809_ = lean_nat_dec_lt(v___x_1807_, v_num_1808_);
if (v___x_1809_ == 0)
{
lean_object* v___x_1810_; lean_object* v___x_1811_; 
lean_dec(v_num_1808_);
lean_dec_ref(v_e_1737_);
v___x_1810_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__4, &l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__4);
v___x_1811_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__0(v___x_1810_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_);
return v___x_1811_;
}
else
{
lean_object* v___f_1812_; lean_object* v___x_1813_; uint8_t v___x_1814_; lean_object* v___x_1815_; 
v___f_1812_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___lam__0___boxed), 7, 0);
v___x_1813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1813_, 0, v_num_1808_);
v___x_1814_ = 0;
v___x_1815_ = l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg(v_e_1737_, v___x_1813_, v___f_1812_, v___x_1814_, v___x_1809_, v___x_1814_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_);
lean_dec_ref(v___x_1813_);
return v___x_1815_;
}
}
}
else
{
lean_object* v___x_1816_; 
v___x_1816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1816_, 0, v_e_1737_);
return v___x_1816_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___lam__0(lean_object* v_xs_1817_, lean_object* v_b_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_){
_start:
{
lean_object* v___x_1824_; 
v___x_1824_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet(v_b_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_);
if (lean_obj_tag(v___x_1824_) == 0)
{
lean_object* v_a_1825_; uint8_t v___x_1826_; uint8_t v___x_1827_; lean_object* v___x_1828_; 
v_a_1825_ = lean_ctor_get(v___x_1824_, 0);
lean_inc(v_a_1825_);
lean_dec_ref(v___x_1824_);
v___x_1826_ = 0;
v___x_1827_ = 1;
v___x_1828_ = l_Lean_Meta_mkLetFVars(v_xs_1817_, v_a_1825_, v___x_1826_, v___x_1826_, v___x_1827_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_);
return v___x_1828_;
}
else
{
return v___x_1824_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___boxed(lean_object* v_e_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_){
_start:
{
lean_object* v_res_1835_; 
v_res_1835_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet(v_e_1829_, v_a_1830_, v_a_1831_, v_a_1832_, v_a_1833_);
lean_dec(v_a_1833_);
lean_dec_ref(v_a_1832_);
lean_dec(v_a_1831_);
lean_dec_ref(v_a_1830_);
return v_res_1835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramLet___redArg(lean_object* v_e_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_){
_start:
{
uint8_t v___y_1843_; uint8_t v___x_1865_; 
v___x_1865_ = l_Lean_Expr_isLet(v_e_1836_);
if (v___x_1865_ == 0)
{
uint8_t v___x_1866_; 
v___x_1866_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_anyLetValueIsWfParam(v_e_1836_);
v___y_1843_ = v___x_1866_;
goto v___jp_1842_;
}
else
{
v___y_1843_ = v___x_1865_;
goto v___jp_1842_;
}
v___jp_1842_:
{
if (v___y_1843_ == 0)
{
lean_object* v___x_1844_; lean_object* v___x_1845_; 
lean_dec_ref(v_e_1836_);
v___x_1844_ = ((lean_object*)(l_Lean_Elab_WF_paramProj___closed__0));
v___x_1845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1845_, 0, v___x_1844_);
return v___x_1845_;
}
else
{
lean_object* v___x_1846_; 
v___x_1846_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet(v_e_1836_, v_a_1837_, v_a_1838_, v_a_1839_, v_a_1840_);
if (lean_obj_tag(v___x_1846_) == 0)
{
lean_object* v_a_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1856_; 
v_a_1847_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_1856_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1849_ = v___x_1846_;
v_isShared_1850_ = v_isSharedCheck_1856_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_a_1847_);
lean_dec(v___x_1846_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1856_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1854_; 
v___x_1851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1851_, 0, v_a_1847_);
v___x_1852_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1851_);
if (v_isShared_1850_ == 0)
{
lean_ctor_set(v___x_1849_, 0, v___x_1852_);
v___x_1854_ = v___x_1849_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v___x_1852_);
v___x_1854_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
return v___x_1854_;
}
}
}
else
{
lean_object* v_a_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1864_; 
v_a_1857_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_1864_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1859_ = v___x_1846_;
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_a_1857_);
lean_dec(v___x_1846_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v___x_1862_; 
if (v_isShared_1860_ == 0)
{
v___x_1862_ = v___x_1859_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v_a_1857_);
v___x_1862_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
return v___x_1862_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramLet___redArg___boxed(lean_object* v_e_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_){
_start:
{
lean_object* v_res_1873_; 
v_res_1873_ = l_Lean_Elab_WF_paramLet___redArg(v_e_1867_, v_a_1868_, v_a_1869_, v_a_1870_, v_a_1871_);
lean_dec(v_a_1871_);
lean_dec_ref(v_a_1870_);
lean_dec(v_a_1869_);
lean_dec_ref(v_a_1868_);
return v_res_1873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramLet(lean_object* v_e_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_){
_start:
{
lean_object* v___x_1883_; 
v___x_1883_ = l_Lean_Elab_WF_paramLet___redArg(v_e_1874_, v_a_1878_, v_a_1879_, v_a_1880_, v_a_1881_);
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramLet___boxed(lean_object* v_e_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_){
_start:
{
lean_object* v_res_1893_; 
v_res_1893_ = l_Lean_Elab_WF_paramLet(v_e_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_);
lean_dec(v_a_1891_);
lean_dec_ref(v_a_1890_);
lean_dec(v_a_1889_);
lean_dec_ref(v_a_1888_);
lean_dec(v_a_1887_);
lean_dec_ref(v_a_1886_);
lean_dec(v_a_1885_);
return v_res_1893_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__60_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12_(){
_start:
{
lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; 
v___x_1901_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__60___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12_));
v___x_1902_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__26___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_12_));
v___x_1903_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_paramLet___boxed), 9, 0);
v___x_1904_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1901_, v___x_1902_, v___x_1903_);
return v___x_1904_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__60_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12____boxed(lean_object* v_a_1905_){
_start:
{
lean_object* v_res_1906_; 
v_res_1906_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__60_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12_();
return v_res_1906_;
}
}
static lean_object* _init_l_Lean_Elab_WF_paramLet___regBuiltin_Lean_Elab_WF_paramLet_declare__1___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_14_(void){
_start:
{
lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___x_1907_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_paramLet___boxed), 9, 0);
v___x_1908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1908_, 0, v___x_1907_);
return v___x_1908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramLet___regBuiltin_Lean_Elab_WF_paramLet_declare__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_14_(){
_start:
{
lean_object* v___x_1910_; uint8_t v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; 
v___x_1910_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__60___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12_));
v___x_1911_ = 1;
v___x_1912_ = lean_obj_once(&l_Lean_Elab_WF_paramLet___regBuiltin_Lean_Elab_WF_paramLet_declare__1___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_14_, &l_Lean_Elab_WF_paramLet___regBuiltin_Lean_Elab_WF_paramLet_declare__1___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_14__once, _init_l_Lean_Elab_WF_paramLet___regBuiltin_Lean_Elab_WF_paramLet_declare__1___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_14_);
v___x_1913_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1910_, v___x_1911_, v___x_1912_);
return v___x_1913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramLet___regBuiltin_Lean_Elab_WF_paramLet_declare__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_14____boxed(lean_object* v_a_1914_){
_start:
{
lean_object* v_res_1915_; 
v_res_1915_ = l_Lean_Elab_WF_paramLet___regBuiltin_Lean_Elab_WF_paramLet_declare__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_14_();
return v_res_1915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__0___redArg(lean_object* v_lctx_1916_, lean_object* v_x_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_){
_start:
{
lean_object* v_keyedConfig_1923_; uint8_t v_trackZetaDelta_1924_; lean_object* v_zetaDeltaSet_1925_; lean_object* v_localInstances_1926_; lean_object* v_defEqCtx_x3f_1927_; lean_object* v_synthPendingDepth_1928_; lean_object* v_canUnfold_x3f_1929_; uint8_t v_univApprox_1930_; uint8_t v_inTypeClassResolution_1931_; uint8_t v_cacheInferType_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; 
v_keyedConfig_1923_ = lean_ctor_get(v___y_1918_, 0);
v_trackZetaDelta_1924_ = lean_ctor_get_uint8(v___y_1918_, sizeof(void*)*7);
v_zetaDeltaSet_1925_ = lean_ctor_get(v___y_1918_, 1);
v_localInstances_1926_ = lean_ctor_get(v___y_1918_, 3);
v_defEqCtx_x3f_1927_ = lean_ctor_get(v___y_1918_, 4);
v_synthPendingDepth_1928_ = lean_ctor_get(v___y_1918_, 5);
v_canUnfold_x3f_1929_ = lean_ctor_get(v___y_1918_, 6);
v_univApprox_1930_ = lean_ctor_get_uint8(v___y_1918_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1931_ = lean_ctor_get_uint8(v___y_1918_, sizeof(void*)*7 + 2);
v_cacheInferType_1932_ = lean_ctor_get_uint8(v___y_1918_, sizeof(void*)*7 + 3);
lean_inc(v_canUnfold_x3f_1929_);
lean_inc(v_synthPendingDepth_1928_);
lean_inc(v_defEqCtx_x3f_1927_);
lean_inc_ref(v_localInstances_1926_);
lean_inc(v_zetaDeltaSet_1925_);
lean_inc_ref(v_keyedConfig_1923_);
v___x_1933_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1933_, 0, v_keyedConfig_1923_);
lean_ctor_set(v___x_1933_, 1, v_zetaDeltaSet_1925_);
lean_ctor_set(v___x_1933_, 2, v_lctx_1916_);
lean_ctor_set(v___x_1933_, 3, v_localInstances_1926_);
lean_ctor_set(v___x_1933_, 4, v_defEqCtx_x3f_1927_);
lean_ctor_set(v___x_1933_, 5, v_synthPendingDepth_1928_);
lean_ctor_set(v___x_1933_, 6, v_canUnfold_x3f_1929_);
lean_ctor_set_uint8(v___x_1933_, sizeof(void*)*7, v_trackZetaDelta_1924_);
lean_ctor_set_uint8(v___x_1933_, sizeof(void*)*7 + 1, v_univApprox_1930_);
lean_ctor_set_uint8(v___x_1933_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1931_);
lean_ctor_set_uint8(v___x_1933_, sizeof(void*)*7 + 3, v_cacheInferType_1932_);
lean_inc(v___y_1921_);
lean_inc_ref(v___y_1920_);
lean_inc(v___y_1919_);
v___x_1934_ = lean_apply_5(v_x_1917_, v___x_1933_, v___y_1919_, v___y_1920_, v___y_1921_, lean_box(0));
return v___x_1934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__0___redArg___boxed(lean_object* v_lctx_1935_, lean_object* v_x_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_){
_start:
{
lean_object* v_res_1942_; 
v_res_1942_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__0___redArg(v_lctx_1935_, v_x_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_);
lean_dec(v___y_1940_);
lean_dec_ref(v___y_1939_);
lean_dec(v___y_1938_);
lean_dec_ref(v___y_1937_);
return v_res_1942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__0(lean_object* v_00_u03b1_1943_, lean_object* v_lctx_1944_, lean_object* v_x_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_){
_start:
{
lean_object* v___x_1951_; 
v___x_1951_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__0___redArg(v_lctx_1944_, v_x_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_);
return v___x_1951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__0___boxed(lean_object* v_00_u03b1_1952_, lean_object* v_lctx_1953_, lean_object* v_x_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_){
_start:
{
lean_object* v_res_1960_; 
v_res_1960_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__0(v_00_u03b1_1952_, v_lctx_1953_, v_x_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_);
lean_dec(v___y_1958_);
lean_dec_ref(v___y_1957_);
lean_dec(v___y_1956_);
lean_dec_ref(v___y_1955_);
return v_res_1960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__2___redArg(lean_object* v_e_1961_, lean_object* v_k_1962_, uint8_t v_cleanupAnnotations_1963_, uint8_t v_preserveNondepLet_1964_, uint8_t v_nondepLetOnly_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_){
_start:
{
lean_object* v___f_1971_; uint8_t v___x_1972_; uint8_t v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; 
v___f_1971_ = lean_alloc_closure((void*)(l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1971_, 0, v_k_1962_);
v___x_1972_ = 0;
v___x_1973_ = 1;
v___x_1974_ = lean_box(0);
v___x_1975_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_1961_, v___x_1972_, v___x_1973_, v_preserveNondepLet_1964_, v_nondepLetOnly_1965_, v___x_1974_, v___f_1971_, v_cleanupAnnotations_1963_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_);
if (lean_obj_tag(v___x_1975_) == 0)
{
lean_object* v_a_1976_; lean_object* v___x_1978_; uint8_t v_isShared_1979_; uint8_t v_isSharedCheck_1983_; 
v_a_1976_ = lean_ctor_get(v___x_1975_, 0);
v_isSharedCheck_1983_ = !lean_is_exclusive(v___x_1975_);
if (v_isSharedCheck_1983_ == 0)
{
v___x_1978_ = v___x_1975_;
v_isShared_1979_ = v_isSharedCheck_1983_;
goto v_resetjp_1977_;
}
else
{
lean_inc(v_a_1976_);
lean_dec(v___x_1975_);
v___x_1978_ = lean_box(0);
v_isShared_1979_ = v_isSharedCheck_1983_;
goto v_resetjp_1977_;
}
v_resetjp_1977_:
{
lean_object* v___x_1981_; 
if (v_isShared_1979_ == 0)
{
v___x_1981_ = v___x_1978_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v_a_1976_);
v___x_1981_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
return v___x_1981_;
}
}
}
else
{
lean_object* v_a_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_1991_; 
v_a_1984_ = lean_ctor_get(v___x_1975_, 0);
v_isSharedCheck_1991_ = !lean_is_exclusive(v___x_1975_);
if (v_isSharedCheck_1991_ == 0)
{
v___x_1986_ = v___x_1975_;
v_isShared_1987_ = v_isSharedCheck_1991_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_a_1984_);
lean_dec(v___x_1975_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_1991_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
lean_object* v___x_1989_; 
if (v_isShared_1987_ == 0)
{
v___x_1989_ = v___x_1986_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v_a_1984_);
v___x_1989_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
return v___x_1989_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__2___redArg___boxed(lean_object* v_e_1992_, lean_object* v_k_1993_, lean_object* v_cleanupAnnotations_1994_, lean_object* v_preserveNondepLet_1995_, lean_object* v_nondepLetOnly_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2002_; uint8_t v_preserveNondepLet_boxed_2003_; uint8_t v_nondepLetOnly_boxed_2004_; lean_object* v_res_2005_; 
v_cleanupAnnotations_boxed_2002_ = lean_unbox(v_cleanupAnnotations_1994_);
v_preserveNondepLet_boxed_2003_ = lean_unbox(v_preserveNondepLet_1995_);
v_nondepLetOnly_boxed_2004_ = lean_unbox(v_nondepLetOnly_1996_);
v_res_2005_ = l_Lean_Meta_letTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__2___redArg(v_e_1992_, v_k_1993_, v_cleanupAnnotations_boxed_2002_, v_preserveNondepLet_boxed_2003_, v_nondepLetOnly_boxed_2004_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_);
lean_dec(v___y_2000_);
lean_dec_ref(v___y_1999_);
lean_dec(v___y_1998_);
lean_dec_ref(v___y_1997_);
return v_res_2005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__2(lean_object* v_00_u03b1_2006_, lean_object* v_e_2007_, lean_object* v_k_2008_, uint8_t v_cleanupAnnotations_2009_, uint8_t v_preserveNondepLet_2010_, uint8_t v_nondepLetOnly_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_){
_start:
{
lean_object* v___x_2017_; 
v___x_2017_ = l_Lean_Meta_letTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__2___redArg(v_e_2007_, v_k_2008_, v_cleanupAnnotations_2009_, v_preserveNondepLet_2010_, v_nondepLetOnly_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_);
return v___x_2017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__2___boxed(lean_object* v_00_u03b1_2018_, lean_object* v_e_2019_, lean_object* v_k_2020_, lean_object* v_cleanupAnnotations_2021_, lean_object* v_preserveNondepLet_2022_, lean_object* v_nondepLetOnly_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2029_; uint8_t v_preserveNondepLet_boxed_2030_; uint8_t v_nondepLetOnly_boxed_2031_; lean_object* v_res_2032_; 
v_cleanupAnnotations_boxed_2029_ = lean_unbox(v_cleanupAnnotations_2021_);
v_preserveNondepLet_boxed_2030_ = lean_unbox(v_preserveNondepLet_2022_);
v_nondepLetOnly_boxed_2031_ = lean_unbox(v_nondepLetOnly_2023_);
v_res_2032_ = l_Lean_Meta_letTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__2(v_00_u03b1_2018_, v_e_2019_, v_k_2020_, v_cleanupAnnotations_boxed_2029_, v_preserveNondepLet_boxed_2030_, v_nondepLetOnly_boxed_2031_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_);
lean_dec(v___y_2027_);
lean_dec_ref(v___y_2026_);
lean_dec(v___y_2025_);
lean_dec_ref(v___y_2024_);
return v_res_2032_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__0(lean_object* v_e_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_){
_start:
{
lean_object* v___x_2039_; lean_object* v___x_2040_; 
v___x_2039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2039_, 0, v_e_2033_);
v___x_2040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2040_, 0, v___x_2039_);
return v___x_2040_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__0___boxed(lean_object* v_e_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_){
_start:
{
lean_object* v_res_2047_; 
v_res_2047_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__0(v_e_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_);
lean_dec(v___y_2045_);
lean_dec_ref(v___y_2044_);
lean_dec(v___y_2043_);
lean_dec_ref(v___y_2042_);
return v_res_2047_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__1(lean_object* v_as_2048_, size_t v_i_2049_, size_t v_stop_2050_, lean_object* v_b_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_){
_start:
{
uint8_t v___x_2057_; 
v___x_2057_ = lean_usize_dec_eq(v_i_2049_, v_stop_2050_);
if (v___x_2057_ == 0)
{
lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; 
v___x_2058_ = lean_array_uget_borrowed(v_as_2048_, v_i_2049_);
v___x_2059_ = l_Lean_Expr_fvarId_x21(v___x_2058_);
lean_inc_ref(v___y_2052_);
v___x_2060_ = l_Lean_FVarId_getDecl___redArg(v___x_2059_, v___y_2052_, v___y_2054_, v___y_2055_);
if (lean_obj_tag(v___x_2060_) == 0)
{
lean_object* v_a_2061_; uint8_t v_a_2063_; uint8_t v___x_2069_; 
v_a_2061_ = lean_ctor_get(v___x_2060_, 0);
lean_inc(v_a_2061_);
lean_dec_ref(v___x_2060_);
v___x_2069_ = l_Lean_LocalDecl_isNondep(v_a_2061_);
if (v___x_2069_ == 0)
{
v_a_2063_ = v___x_2069_;
goto v___jp_2062_;
}
else
{
lean_object* v___x_2070_; lean_object* v___x_2071_; 
v___x_2070_ = l_Lean_LocalDecl_type(v_a_2061_);
v___x_2071_ = l_Lean_Meta_isProp(v___x_2070_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_);
if (lean_obj_tag(v___x_2071_) == 0)
{
lean_object* v_a_2072_; uint8_t v___x_2073_; 
v_a_2072_ = lean_ctor_get(v___x_2071_, 0);
lean_inc(v_a_2072_);
lean_dec_ref(v___x_2071_);
v___x_2073_ = lean_unbox(v_a_2072_);
lean_dec(v_a_2072_);
v_a_2063_ = v___x_2073_;
goto v___jp_2062_;
}
else
{
lean_object* v_a_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2081_; 
lean_dec(v_a_2061_);
lean_dec_ref(v_b_2051_);
v_a_2074_ = lean_ctor_get(v___x_2071_, 0);
v_isSharedCheck_2081_ = !lean_is_exclusive(v___x_2071_);
if (v_isSharedCheck_2081_ == 0)
{
v___x_2076_ = v___x_2071_;
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_a_2074_);
lean_dec(v___x_2071_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v___x_2079_; 
if (v_isShared_2077_ == 0)
{
v___x_2079_ = v___x_2076_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v_a_2074_);
v___x_2079_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
return v___x_2079_;
}
}
}
}
v___jp_2062_:
{
lean_object* v___x_2064_; lean_object* v___x_2065_; size_t v___x_2066_; size_t v___x_2067_; 
v___x_2064_ = l_Lean_LocalDecl_setNondep(v_a_2061_, v_a_2063_);
v___x_2065_ = l_Lean_LocalContext_addDecl(v_b_2051_, v___x_2064_);
v___x_2066_ = ((size_t)1ULL);
v___x_2067_ = lean_usize_add(v_i_2049_, v___x_2066_);
v_i_2049_ = v___x_2067_;
v_b_2051_ = v___x_2065_;
goto _start;
}
}
else
{
lean_object* v_a_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2089_; 
lean_dec_ref(v_b_2051_);
v_a_2082_ = lean_ctor_get(v___x_2060_, 0);
v_isSharedCheck_2089_ = !lean_is_exclusive(v___x_2060_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2084_ = v___x_2060_;
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_a_2082_);
lean_dec(v___x_2060_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2087_; 
if (v_isShared_2085_ == 0)
{
v___x_2087_ = v___x_2084_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v_a_2082_);
v___x_2087_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
return v___x_2087_;
}
}
}
}
else
{
lean_object* v___x_2090_; 
v___x_2090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2090_, 0, v_b_2051_);
return v___x_2090_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__1___boxed(lean_object* v_as_2091_, lean_object* v_i_2092_, lean_object* v_stop_2093_, lean_object* v_b_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_){
_start:
{
size_t v_i_boxed_2100_; size_t v_stop_boxed_2101_; lean_object* v_res_2102_; 
v_i_boxed_2100_ = lean_unbox_usize(v_i_2092_);
lean_dec(v_i_2092_);
v_stop_boxed_2101_ = lean_unbox_usize(v_stop_2093_);
lean_dec(v_stop_2093_);
v_res_2102_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__1(v_as_2091_, v_i_boxed_2100_, v_stop_boxed_2101_, v_b_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_);
lean_dec(v___y_2098_);
lean_dec_ref(v___y_2097_);
lean_dec(v___y_2096_);
lean_dec_ref(v___y_2095_);
lean_dec_ref(v_as_2091_);
return v_res_2102_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__1(uint8_t v_a_2103_, lean_object* v_lctx_2104_, lean_object* v_xs_2105_, lean_object* v_b_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_){
_start:
{
lean_object* v_a_2113_; lean_object* v___y_2121_; lean_object* v___x_2131_; lean_object* v___x_2132_; uint8_t v___x_2133_; 
v___x_2131_ = lean_unsigned_to_nat(0u);
v___x_2132_ = lean_array_get_size(v_xs_2105_);
v___x_2133_ = lean_nat_dec_lt(v___x_2131_, v___x_2132_);
if (v___x_2133_ == 0)
{
v_a_2113_ = v_lctx_2104_;
goto v___jp_2112_;
}
else
{
uint8_t v___x_2134_; 
v___x_2134_ = lean_nat_dec_le(v___x_2132_, v___x_2132_);
if (v___x_2134_ == 0)
{
if (v___x_2133_ == 0)
{
v_a_2113_ = v_lctx_2104_;
goto v___jp_2112_;
}
else
{
size_t v___x_2135_; size_t v___x_2136_; lean_object* v___x_2137_; 
v___x_2135_ = ((size_t)0ULL);
v___x_2136_ = lean_usize_of_nat(v___x_2132_);
v___x_2137_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__1(v_xs_2105_, v___x_2135_, v___x_2136_, v_lctx_2104_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
v___y_2121_ = v___x_2137_;
goto v___jp_2120_;
}
}
else
{
size_t v___x_2138_; size_t v___x_2139_; lean_object* v___x_2140_; 
v___x_2138_ = ((size_t)0ULL);
v___x_2139_ = lean_usize_of_nat(v___x_2132_);
v___x_2140_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__1(v_xs_2105_, v___x_2138_, v___x_2139_, v_lctx_2104_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
v___y_2121_ = v___x_2140_;
goto v___jp_2120_;
}
}
v___jp_2112_:
{
uint8_t v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; 
v___x_2114_ = 1;
v___x_2115_ = lean_box(v_a_2103_);
v___x_2116_ = lean_box(v_a_2103_);
v___x_2117_ = lean_box(v___x_2114_);
v___x_2118_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLetFVars___boxed), 10, 5);
lean_closure_set(v___x_2118_, 0, v_xs_2105_);
lean_closure_set(v___x_2118_, 1, v_b_2106_);
lean_closure_set(v___x_2118_, 2, v___x_2115_);
lean_closure_set(v___x_2118_, 3, v___x_2116_);
lean_closure_set(v___x_2118_, 4, v___x_2117_);
v___x_2119_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__0___redArg(v_a_2113_, v___x_2118_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
return v___x_2119_;
}
v___jp_2120_:
{
if (lean_obj_tag(v___y_2121_) == 0)
{
lean_object* v_a_2122_; 
v_a_2122_ = lean_ctor_get(v___y_2121_, 0);
lean_inc(v_a_2122_);
lean_dec_ref(v___y_2121_);
v_a_2113_ = v_a_2122_;
goto v___jp_2112_;
}
else
{
lean_object* v_a_2123_; lean_object* v___x_2125_; uint8_t v_isShared_2126_; uint8_t v_isSharedCheck_2130_; 
lean_dec_ref(v_b_2106_);
lean_dec_ref(v_xs_2105_);
v_a_2123_ = lean_ctor_get(v___y_2121_, 0);
v_isSharedCheck_2130_ = !lean_is_exclusive(v___y_2121_);
if (v_isSharedCheck_2130_ == 0)
{
v___x_2125_ = v___y_2121_;
v_isShared_2126_ = v_isSharedCheck_2130_;
goto v_resetjp_2124_;
}
else
{
lean_inc(v_a_2123_);
lean_dec(v___y_2121_);
v___x_2125_ = lean_box(0);
v_isShared_2126_ = v_isSharedCheck_2130_;
goto v_resetjp_2124_;
}
v_resetjp_2124_:
{
lean_object* v___x_2128_; 
if (v_isShared_2126_ == 0)
{
v___x_2128_ = v___x_2125_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v_a_2123_);
v___x_2128_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
return v___x_2128_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__1___boxed(lean_object* v_a_2141_, lean_object* v_lctx_2142_, lean_object* v_xs_2143_, lean_object* v_b_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_){
_start:
{
uint8_t v_a_10678__boxed_2150_; lean_object* v_res_2151_; 
v_a_10678__boxed_2150_ = lean_unbox(v_a_2141_);
v_res_2151_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__1(v_a_10678__boxed_2150_, v_lctx_2142_, v_xs_2143_, v_b_2144_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_);
lean_dec(v___y_2148_);
lean_dec_ref(v___y_2147_);
lean_dec(v___y_2146_);
lean_dec_ref(v___y_2145_);
return v_res_2151_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__2(lean_object* v_e_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_){
_start:
{
lean_object* v___x_2158_; 
lean_inc_ref(v_e_2152_);
v___x_2158_ = l_Lean_Meta_isProof(v_e_2152_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_);
if (lean_obj_tag(v___x_2158_) == 0)
{
lean_object* v_a_2159_; lean_object* v___x_2161_; uint8_t v_isShared_2162_; uint8_t v_isSharedCheck_2196_; 
v_a_2159_ = lean_ctor_get(v___x_2158_, 0);
v_isSharedCheck_2196_ = !lean_is_exclusive(v___x_2158_);
if (v_isSharedCheck_2196_ == 0)
{
v___x_2161_ = v___x_2158_;
v_isShared_2162_ = v_isSharedCheck_2196_;
goto v_resetjp_2160_;
}
else
{
lean_inc(v_a_2159_);
lean_dec(v___x_2158_);
v___x_2161_ = lean_box(0);
v_isShared_2162_ = v_isSharedCheck_2196_;
goto v_resetjp_2160_;
}
v_resetjp_2160_:
{
uint8_t v___x_2163_; 
v___x_2163_ = lean_unbox(v_a_2159_);
if (v___x_2163_ == 0)
{
uint8_t v___x_2164_; 
v___x_2164_ = l_Lean_Expr_isLet(v_e_2152_);
if (v___x_2164_ == 0)
{
lean_object* v___x_2165_; lean_object* v___x_2167_; 
lean_dec(v_a_2159_);
lean_dec_ref(v___y_2153_);
lean_dec_ref(v_e_2152_);
v___x_2165_ = ((lean_object*)(l_Lean_Elab_WF_paramProj___closed__0));
if (v_isShared_2162_ == 0)
{
lean_ctor_set(v___x_2161_, 0, v___x_2165_);
v___x_2167_ = v___x_2161_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v___x_2165_);
v___x_2167_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
return v___x_2167_;
}
}
else
{
lean_object* v_lctx_2169_; lean_object* v___f_2170_; uint8_t v___x_2171_; uint8_t v___x_2172_; lean_object* v___x_2173_; 
lean_del_object(v___x_2161_);
v_lctx_2169_ = lean_ctor_get(v___y_2153_, 2);
lean_inc_ref(v_lctx_2169_);
lean_inc(v_a_2159_);
v___f_2170_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__1___boxed), 9, 2);
lean_closure_set(v___f_2170_, 0, v_a_2159_);
lean_closure_set(v___f_2170_, 1, v_lctx_2169_);
v___x_2171_ = lean_unbox(v_a_2159_);
v___x_2172_ = lean_unbox(v_a_2159_);
lean_dec(v_a_2159_);
v___x_2173_ = l_Lean_Meta_letTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__2___redArg(v_e_2152_, v___f_2170_, v___x_2171_, v___x_2164_, v___x_2172_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_);
lean_dec_ref(v___y_2153_);
if (lean_obj_tag(v___x_2173_) == 0)
{
lean_object* v_a_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2183_; 
v_a_2174_ = lean_ctor_get(v___x_2173_, 0);
v_isSharedCheck_2183_ = !lean_is_exclusive(v___x_2173_);
if (v_isSharedCheck_2183_ == 0)
{
v___x_2176_ = v___x_2173_;
v_isShared_2177_ = v_isSharedCheck_2183_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_a_2174_);
lean_dec(v___x_2173_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2183_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2181_; 
v___x_2178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2178_, 0, v_a_2174_);
v___x_2179_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2179_, 0, v___x_2178_);
if (v_isShared_2177_ == 0)
{
lean_ctor_set(v___x_2176_, 0, v___x_2179_);
v___x_2181_ = v___x_2176_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v___x_2179_);
v___x_2181_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
return v___x_2181_;
}
}
}
else
{
lean_object* v_a_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2191_; 
v_a_2184_ = lean_ctor_get(v___x_2173_, 0);
v_isSharedCheck_2191_ = !lean_is_exclusive(v___x_2173_);
if (v_isSharedCheck_2191_ == 0)
{
v___x_2186_ = v___x_2173_;
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_a_2184_);
lean_dec(v___x_2173_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
lean_object* v___x_2189_; 
if (v_isShared_2187_ == 0)
{
v___x_2189_ = v___x_2186_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v_a_2184_);
v___x_2189_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
return v___x_2189_;
}
}
}
}
}
else
{
lean_object* v___x_2192_; lean_object* v___x_2194_; 
lean_dec(v_a_2159_);
lean_dec_ref(v___y_2153_);
v___x_2192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2192_, 0, v_e_2152_);
if (v_isShared_2162_ == 0)
{
lean_ctor_set(v___x_2161_, 0, v___x_2192_);
v___x_2194_ = v___x_2161_;
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
}
else
{
lean_object* v_a_2197_; lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2204_; 
lean_dec_ref(v___y_2153_);
lean_dec_ref(v_e_2152_);
v_a_2197_ = lean_ctor_get(v___x_2158_, 0);
v_isSharedCheck_2204_ = !lean_is_exclusive(v___x_2158_);
if (v_isSharedCheck_2204_ == 0)
{
v___x_2199_ = v___x_2158_;
v_isShared_2200_ = v_isSharedCheck_2204_;
goto v_resetjp_2198_;
}
else
{
lean_inc(v_a_2197_);
lean_dec(v___x_2158_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__2___boxed(lean_object* v_e_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_){
_start:
{
lean_object* v_res_2211_; 
v_res_2211_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__2(v_e_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_);
lean_dec(v___y_2209_);
lean_dec_ref(v___y_2208_);
lean_dec(v___y_2207_);
return v_res_2211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___lam__0(lean_object* v_00_u03b1_2212_, lean_object* v_x_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_){
_start:
{
lean_object* v___x_2219_; lean_object* v___x_2220_; 
v___x_2219_ = lean_apply_1(v_x_2213_, lean_box(0));
v___x_2220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2220_, 0, v___x_2219_);
return v___x_2220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___lam__0___boxed(lean_object* v_00_u03b1_2221_, lean_object* v_x_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_){
_start:
{
lean_object* v_res_2228_; 
v_res_2228_ = l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___lam__0(v_00_u03b1_2221_, v_x_2222_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_);
lean_dec(v___y_2226_);
lean_dec_ref(v___y_2225_);
lean_dec(v___y_2224_);
lean_dec_ref(v___y_2223_);
return v_res_2228_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__3(void){
_start:
{
lean_object* v___x_2234_; lean_object* v___x_2235_; 
v___x_2234_ = l_Lean_maxRecDepthErrorMessage;
v___x_2235_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2235_, 0, v___x_2234_);
return v___x_2235_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__4(void){
_start:
{
lean_object* v___x_2236_; lean_object* v___x_2237_; 
v___x_2236_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__3);
v___x_2237_ = l_Lean_MessageData_ofFormat(v___x_2236_);
return v___x_2237_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__5(void){
_start:
{
lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; 
v___x_2238_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__4);
v___x_2239_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__2));
v___x_2240_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2240_, 0, v___x_2239_);
lean_ctor_set(v___x_2240_, 1, v___x_2238_);
return v___x_2240_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg(lean_object* v_ref_2241_){
_start:
{
lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; 
v___x_2243_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__5);
v___x_2244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2244_, 0, v_ref_2241_);
lean_ctor_set(v___x_2244_, 1, v___x_2243_);
v___x_2245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2245_, 0, v___x_2244_);
return v___x_2245_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___boxed(lean_object* v_ref_2246_, lean_object* v___y_2247_){
_start:
{
lean_object* v_res_2248_; 
v_res_2248_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg(v_ref_2246_);
return v_res_2248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12___redArg(lean_object* v_x_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_){
_start:
{
lean_object* v___y_2257_; lean_object* v_fileName_2266_; lean_object* v_fileMap_2267_; lean_object* v_options_2268_; lean_object* v_currRecDepth_2269_; lean_object* v_maxRecDepth_2270_; lean_object* v_ref_2271_; lean_object* v_currNamespace_2272_; lean_object* v_openDecls_2273_; lean_object* v_initHeartbeats_2274_; lean_object* v_maxHeartbeats_2275_; lean_object* v_quotContext_2276_; lean_object* v_currMacroScope_2277_; uint8_t v_diag_2278_; lean_object* v_cancelTk_x3f_2279_; uint8_t v_suppressElabErrors_2280_; lean_object* v_inheritedTraceOptions_2281_; uint8_t v___x_2282_; 
v_fileName_2266_ = lean_ctor_get(v___y_2253_, 0);
lean_inc_ref(v_fileName_2266_);
v_fileMap_2267_ = lean_ctor_get(v___y_2253_, 1);
lean_inc_ref(v_fileMap_2267_);
v_options_2268_ = lean_ctor_get(v___y_2253_, 2);
lean_inc_ref(v_options_2268_);
v_currRecDepth_2269_ = lean_ctor_get(v___y_2253_, 3);
lean_inc(v_currRecDepth_2269_);
v_maxRecDepth_2270_ = lean_ctor_get(v___y_2253_, 4);
lean_inc(v_maxRecDepth_2270_);
v_ref_2271_ = lean_ctor_get(v___y_2253_, 5);
lean_inc(v_ref_2271_);
v_currNamespace_2272_ = lean_ctor_get(v___y_2253_, 6);
lean_inc(v_currNamespace_2272_);
v_openDecls_2273_ = lean_ctor_get(v___y_2253_, 7);
lean_inc(v_openDecls_2273_);
v_initHeartbeats_2274_ = lean_ctor_get(v___y_2253_, 8);
lean_inc(v_initHeartbeats_2274_);
v_maxHeartbeats_2275_ = lean_ctor_get(v___y_2253_, 9);
lean_inc(v_maxHeartbeats_2275_);
v_quotContext_2276_ = lean_ctor_get(v___y_2253_, 10);
lean_inc(v_quotContext_2276_);
v_currMacroScope_2277_ = lean_ctor_get(v___y_2253_, 11);
lean_inc(v_currMacroScope_2277_);
v_diag_2278_ = lean_ctor_get_uint8(v___y_2253_, sizeof(void*)*14);
v_cancelTk_x3f_2279_ = lean_ctor_get(v___y_2253_, 12);
lean_inc(v_cancelTk_x3f_2279_);
v_suppressElabErrors_2280_ = lean_ctor_get_uint8(v___y_2253_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2281_ = lean_ctor_get(v___y_2253_, 13);
lean_inc_ref(v_inheritedTraceOptions_2281_);
lean_dec_ref(v___y_2253_);
v___x_2282_ = lean_nat_dec_eq(v_currRecDepth_2269_, v_maxRecDepth_2270_);
if (v___x_2282_ == 0)
{
lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; 
v___x_2283_ = lean_unsigned_to_nat(1u);
v___x_2284_ = lean_nat_add(v_currRecDepth_2269_, v___x_2283_);
lean_dec(v_currRecDepth_2269_);
v___x_2285_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2285_, 0, v_fileName_2266_);
lean_ctor_set(v___x_2285_, 1, v_fileMap_2267_);
lean_ctor_set(v___x_2285_, 2, v_options_2268_);
lean_ctor_set(v___x_2285_, 3, v___x_2284_);
lean_ctor_set(v___x_2285_, 4, v_maxRecDepth_2270_);
lean_ctor_set(v___x_2285_, 5, v_ref_2271_);
lean_ctor_set(v___x_2285_, 6, v_currNamespace_2272_);
lean_ctor_set(v___x_2285_, 7, v_openDecls_2273_);
lean_ctor_set(v___x_2285_, 8, v_initHeartbeats_2274_);
lean_ctor_set(v___x_2285_, 9, v_maxHeartbeats_2275_);
lean_ctor_set(v___x_2285_, 10, v_quotContext_2276_);
lean_ctor_set(v___x_2285_, 11, v_currMacroScope_2277_);
lean_ctor_set(v___x_2285_, 12, v_cancelTk_x3f_2279_);
lean_ctor_set(v___x_2285_, 13, v_inheritedTraceOptions_2281_);
lean_ctor_set_uint8(v___x_2285_, sizeof(void*)*14, v_diag_2278_);
lean_ctor_set_uint8(v___x_2285_, sizeof(void*)*14 + 1, v_suppressElabErrors_2280_);
lean_inc(v___y_2254_);
lean_inc(v___y_2252_);
lean_inc_ref(v___y_2251_);
lean_inc(v___y_2250_);
v___x_2286_ = lean_apply_6(v_x_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___x_2285_, v___y_2254_, lean_box(0));
v___y_2257_ = v___x_2286_;
goto v___jp_2256_;
}
else
{
lean_object* v___x_2287_; 
lean_dec_ref(v_inheritedTraceOptions_2281_);
lean_dec(v_cancelTk_x3f_2279_);
lean_dec(v_currMacroScope_2277_);
lean_dec(v_quotContext_2276_);
lean_dec(v_maxHeartbeats_2275_);
lean_dec(v_initHeartbeats_2274_);
lean_dec(v_openDecls_2273_);
lean_dec(v_currNamespace_2272_);
lean_dec(v_maxRecDepth_2270_);
lean_dec(v_currRecDepth_2269_);
lean_dec_ref(v_options_2268_);
lean_dec_ref(v_fileMap_2267_);
lean_dec_ref(v_fileName_2266_);
lean_dec_ref(v_x_2249_);
v___x_2287_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg(v_ref_2271_);
v___y_2257_ = v___x_2287_;
goto v___jp_2256_;
}
v___jp_2256_:
{
if (lean_obj_tag(v___y_2257_) == 0)
{
return v___y_2257_;
}
else
{
lean_object* v_a_2258_; lean_object* v___x_2260_; uint8_t v_isShared_2261_; uint8_t v_isSharedCheck_2265_; 
v_a_2258_ = lean_ctor_get(v___y_2257_, 0);
v_isSharedCheck_2265_ = !lean_is_exclusive(v___y_2257_);
if (v_isSharedCheck_2265_ == 0)
{
v___x_2260_ = v___y_2257_;
v_isShared_2261_ = v_isSharedCheck_2265_;
goto v_resetjp_2259_;
}
else
{
lean_inc(v_a_2258_);
lean_dec(v___y_2257_);
v___x_2260_ = lean_box(0);
v_isShared_2261_ = v_isSharedCheck_2265_;
goto v_resetjp_2259_;
}
v_resetjp_2259_:
{
lean_object* v___x_2263_; 
if (v_isShared_2261_ == 0)
{
v___x_2263_ = v___x_2260_;
goto v_reusejp_2262_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v_a_2258_);
v___x_2263_ = v_reuseFailAlloc_2264_;
goto v_reusejp_2262_;
}
v_reusejp_2262_:
{
return v___x_2263_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12___redArg___boxed(lean_object* v_x_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_){
_start:
{
lean_object* v_res_2295_; 
v_res_2295_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12___redArg(v_x_2288_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_);
lean_dec(v___y_2293_);
lean_dec(v___y_2291_);
lean_dec_ref(v___y_2290_);
lean_dec(v___y_2289_);
return v_res_2295_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7_spec__8___redArg(lean_object* v_a_2296_, lean_object* v_x_2297_){
_start:
{
if (lean_obj_tag(v_x_2297_) == 0)
{
lean_object* v___x_2298_; 
v___x_2298_ = lean_box(0);
return v___x_2298_;
}
else
{
lean_object* v_key_2299_; lean_object* v_value_2300_; lean_object* v_tail_2301_; uint8_t v___x_2302_; 
v_key_2299_ = lean_ctor_get(v_x_2297_, 0);
v_value_2300_ = lean_ctor_get(v_x_2297_, 1);
v_tail_2301_ = lean_ctor_get(v_x_2297_, 2);
v___x_2302_ = l_Lean_ExprStructEq_beq(v_key_2299_, v_a_2296_);
if (v___x_2302_ == 0)
{
v_x_2297_ = v_tail_2301_;
goto _start;
}
else
{
lean_object* v___x_2304_; 
lean_inc(v_value_2300_);
v___x_2304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2304_, 0, v_value_2300_);
return v___x_2304_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7_spec__8___redArg___boxed(lean_object* v_a_2305_, lean_object* v_x_2306_){
_start:
{
lean_object* v_res_2307_; 
v_res_2307_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7_spec__8___redArg(v_a_2305_, v_x_2306_);
lean_dec(v_x_2306_);
lean_dec_ref(v_a_2305_);
return v_res_2307_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___redArg(lean_object* v_m_2308_, lean_object* v_a_2309_){
_start:
{
lean_object* v_buckets_2310_; lean_object* v___x_2311_; uint64_t v___x_2312_; uint64_t v___x_2313_; uint64_t v___x_2314_; uint64_t v_fold_2315_; uint64_t v___x_2316_; uint64_t v___x_2317_; uint64_t v___x_2318_; size_t v___x_2319_; size_t v___x_2320_; size_t v___x_2321_; size_t v___x_2322_; size_t v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; 
v_buckets_2310_ = lean_ctor_get(v_m_2308_, 1);
v___x_2311_ = lean_array_get_size(v_buckets_2310_);
v___x_2312_ = l_Lean_ExprStructEq_hash(v_a_2309_);
v___x_2313_ = 32ULL;
v___x_2314_ = lean_uint64_shift_right(v___x_2312_, v___x_2313_);
v_fold_2315_ = lean_uint64_xor(v___x_2312_, v___x_2314_);
v___x_2316_ = 16ULL;
v___x_2317_ = lean_uint64_shift_right(v_fold_2315_, v___x_2316_);
v___x_2318_ = lean_uint64_xor(v_fold_2315_, v___x_2317_);
v___x_2319_ = lean_uint64_to_usize(v___x_2318_);
v___x_2320_ = lean_usize_of_nat(v___x_2311_);
v___x_2321_ = ((size_t)1ULL);
v___x_2322_ = lean_usize_sub(v___x_2320_, v___x_2321_);
v___x_2323_ = lean_usize_land(v___x_2319_, v___x_2322_);
v___x_2324_ = lean_array_uget_borrowed(v_buckets_2310_, v___x_2323_);
v___x_2325_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7_spec__8___redArg(v_a_2309_, v___x_2324_);
return v___x_2325_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___redArg___boxed(lean_object* v_m_2326_, lean_object* v_a_2327_){
_start:
{
lean_object* v_res_2328_; 
v_res_2328_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___redArg(v_m_2326_, v_a_2327_);
lean_dec_ref(v_a_2327_);
lean_dec_ref(v_m_2326_);
return v_res_2328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg___lam__0(lean_object* v_k_2329_, lean_object* v___y_2330_, lean_object* v_b_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_){
_start:
{
lean_object* v___x_2337_; 
lean_inc(v___y_2335_);
lean_inc_ref(v___y_2334_);
lean_inc(v___y_2333_);
lean_inc_ref(v___y_2332_);
lean_inc(v___y_2330_);
v___x_2337_ = lean_apply_7(v_k_2329_, v_b_2331_, v___y_2330_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_, lean_box(0));
return v___x_2337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg___lam__0___boxed(lean_object* v_k_2338_, lean_object* v___y_2339_, lean_object* v_b_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_){
_start:
{
lean_object* v_res_2346_; 
v_res_2346_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg___lam__0(v_k_2338_, v___y_2339_, v_b_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_);
lean_dec(v___y_2344_);
lean_dec_ref(v___y_2343_);
lean_dec(v___y_2342_);
lean_dec_ref(v___y_2341_);
lean_dec(v___y_2339_);
return v_res_2346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg(lean_object* v_name_2347_, uint8_t v_bi_2348_, lean_object* v_type_2349_, lean_object* v_k_2350_, uint8_t v_kind_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_){
_start:
{
lean_object* v___f_2358_; lean_object* v___x_2359_; 
lean_inc(v___y_2352_);
v___f_2358_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2358_, 0, v_k_2350_);
lean_closure_set(v___f_2358_, 1, v___y_2352_);
v___x_2359_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2347_, v_bi_2348_, v_type_2349_, v___f_2358_, v_kind_2351_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg___boxed(lean_object* v_name_2368_, lean_object* v_bi_2369_, lean_object* v_type_2370_, lean_object* v_k_2371_, lean_object* v_kind_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_){
_start:
{
uint8_t v_bi_boxed_2379_; uint8_t v_kind_boxed_2380_; lean_object* v_res_2381_; 
v_bi_boxed_2379_ = lean_unbox(v_bi_2369_);
v_kind_boxed_2380_ = lean_unbox(v_kind_2372_);
v_res_2381_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg(v_name_2368_, v_bi_boxed_2379_, v_type_2370_, v_k_2371_, v_kind_boxed_2380_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_);
lean_dec(v___y_2377_);
lean_dec_ref(v___y_2376_);
lean_dec(v___y_2375_);
lean_dec_ref(v___y_2374_);
lean_dec(v___y_2373_);
return v_res_2381_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___lam__2(lean_object* v___x_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_){
_start:
{
lean_object* v___x_2388_; 
v___x_2388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2388_, 0, v___x_2382_);
return v___x_2388_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___lam__2___boxed(lean_object* v___x_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_){
_start:
{
lean_object* v_res_2395_; 
v_res_2395_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___lam__2(v___x_2389_, v___y_2390_, v___y_2391_, v___y_2392_, v___y_2393_);
lean_dec(v___y_2393_);
lean_dec_ref(v___y_2392_);
lean_dec(v___y_2391_);
lean_dec_ref(v___y_2390_);
return v_res_2395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13___redArg(lean_object* v_name_2396_, lean_object* v_type_2397_, lean_object* v_val_2398_, lean_object* v_k_2399_, uint8_t v_nondep_2400_, uint8_t v_kind_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_){
_start:
{
lean_object* v___f_2408_; lean_object* v___x_2409_; 
lean_inc(v___y_2402_);
v___f_2408_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2408_, 0, v_k_2399_);
lean_closure_set(v___f_2408_, 1, v___y_2402_);
v___x_2409_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_2396_, v_type_2397_, v_val_2398_, v___f_2408_, v_nondep_2400_, v_kind_2401_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_);
if (lean_obj_tag(v___x_2409_) == 0)
{
return v___x_2409_;
}
else
{
lean_object* v_a_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2417_; 
v_a_2410_ = lean_ctor_get(v___x_2409_, 0);
v_isSharedCheck_2417_ = !lean_is_exclusive(v___x_2409_);
if (v_isSharedCheck_2417_ == 0)
{
v___x_2412_ = v___x_2409_;
v_isShared_2413_ = v_isSharedCheck_2417_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_a_2410_);
lean_dec(v___x_2409_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2417_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v___x_2415_; 
if (v_isShared_2413_ == 0)
{
v___x_2415_ = v___x_2412_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2416_; 
v_reuseFailAlloc_2416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2416_, 0, v_a_2410_);
v___x_2415_ = v_reuseFailAlloc_2416_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
return v___x_2415_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13___redArg___boxed(lean_object* v_name_2418_, lean_object* v_type_2419_, lean_object* v_val_2420_, lean_object* v_k_2421_, lean_object* v_nondep_2422_, lean_object* v_kind_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_){
_start:
{
uint8_t v_nondep_boxed_2430_; uint8_t v_kind_boxed_2431_; lean_object* v_res_2432_; 
v_nondep_boxed_2430_ = lean_unbox(v_nondep_2422_);
v_kind_boxed_2431_ = lean_unbox(v_kind_2423_);
v_res_2432_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13___redArg(v_name_2418_, v_type_2419_, v_val_2420_, v_k_2421_, v_nondep_boxed_2430_, v_kind_boxed_2431_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_);
lean_dec(v___y_2428_);
lean_dec_ref(v___y_2427_);
lean_dec(v___y_2426_);
lean_dec_ref(v___y_2425_);
lean_dec(v___y_2424_);
return v_res_2432_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__0(lean_object* v_00_u03b1_2433_, lean_object* v_x_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_){
_start:
{
lean_object* v___x_2440_; lean_object* v___x_2441_; 
v___x_2440_ = lean_apply_1(v_x_2434_, lean_box(0));
v___x_2441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2441_, 0, v___x_2440_);
return v___x_2441_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__0___boxed(lean_object* v_00_u03b1_2442_, lean_object* v_x_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_){
_start:
{
lean_object* v_res_2449_; 
v_res_2449_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__0(v_00_u03b1_2442_, v_x_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_);
lean_dec(v___y_2447_);
lean_dec_ref(v___y_2446_);
lean_dec(v___y_2445_);
lean_dec_ref(v___y_2444_);
return v_res_2449_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18___redArg(lean_object* v_a_2450_, lean_object* v_x_2451_){
_start:
{
if (lean_obj_tag(v_x_2451_) == 0)
{
uint8_t v___x_2452_; 
v___x_2452_ = 0;
return v___x_2452_;
}
else
{
lean_object* v_key_2453_; lean_object* v_tail_2454_; uint8_t v___x_2455_; 
v_key_2453_ = lean_ctor_get(v_x_2451_, 0);
v_tail_2454_ = lean_ctor_get(v_x_2451_, 2);
v___x_2455_ = l_Lean_ExprStructEq_beq(v_key_2453_, v_a_2450_);
if (v___x_2455_ == 0)
{
v_x_2451_ = v_tail_2454_;
goto _start;
}
else
{
return v___x_2455_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18___redArg___boxed(lean_object* v_a_2457_, lean_object* v_x_2458_){
_start:
{
uint8_t v_res_2459_; lean_object* v_r_2460_; 
v_res_2459_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18___redArg(v_a_2457_, v_x_2458_);
lean_dec(v_x_2458_);
lean_dec_ref(v_a_2457_);
v_r_2460_ = lean_box(v_res_2459_);
return v_r_2460_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__20___redArg(lean_object* v_a_2461_, lean_object* v_b_2462_, lean_object* v_x_2463_){
_start:
{
if (lean_obj_tag(v_x_2463_) == 0)
{
lean_dec(v_b_2462_);
lean_dec_ref(v_a_2461_);
return v_x_2463_;
}
else
{
lean_object* v_key_2464_; lean_object* v_value_2465_; lean_object* v_tail_2466_; lean_object* v___x_2468_; uint8_t v_isShared_2469_; uint8_t v_isSharedCheck_2478_; 
v_key_2464_ = lean_ctor_get(v_x_2463_, 0);
v_value_2465_ = lean_ctor_get(v_x_2463_, 1);
v_tail_2466_ = lean_ctor_get(v_x_2463_, 2);
v_isSharedCheck_2478_ = !lean_is_exclusive(v_x_2463_);
if (v_isSharedCheck_2478_ == 0)
{
v___x_2468_ = v_x_2463_;
v_isShared_2469_ = v_isSharedCheck_2478_;
goto v_resetjp_2467_;
}
else
{
lean_inc(v_tail_2466_);
lean_inc(v_value_2465_);
lean_inc(v_key_2464_);
lean_dec(v_x_2463_);
v___x_2468_ = lean_box(0);
v_isShared_2469_ = v_isSharedCheck_2478_;
goto v_resetjp_2467_;
}
v_resetjp_2467_:
{
uint8_t v___x_2470_; 
v___x_2470_ = l_Lean_ExprStructEq_beq(v_key_2464_, v_a_2461_);
if (v___x_2470_ == 0)
{
lean_object* v___x_2471_; lean_object* v___x_2473_; 
v___x_2471_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__20___redArg(v_a_2461_, v_b_2462_, v_tail_2466_);
if (v_isShared_2469_ == 0)
{
lean_ctor_set(v___x_2468_, 2, v___x_2471_);
v___x_2473_ = v___x_2468_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v_key_2464_);
lean_ctor_set(v_reuseFailAlloc_2474_, 1, v_value_2465_);
lean_ctor_set(v_reuseFailAlloc_2474_, 2, v___x_2471_);
v___x_2473_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
return v___x_2473_;
}
}
else
{
lean_object* v___x_2476_; 
lean_dec(v_value_2465_);
lean_dec(v_key_2464_);
if (v_isShared_2469_ == 0)
{
lean_ctor_set(v___x_2468_, 1, v_b_2462_);
lean_ctor_set(v___x_2468_, 0, v_a_2461_);
v___x_2476_ = v___x_2468_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v_a_2461_);
lean_ctor_set(v_reuseFailAlloc_2477_, 1, v_b_2462_);
lean_ctor_set(v_reuseFailAlloc_2477_, 2, v_tail_2466_);
v___x_2476_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
return v___x_2476_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19_spec__20_spec__21___redArg(lean_object* v_x_2479_, lean_object* v_x_2480_){
_start:
{
if (lean_obj_tag(v_x_2480_) == 0)
{
return v_x_2479_;
}
else
{
lean_object* v_key_2481_; lean_object* v_value_2482_; lean_object* v_tail_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2506_; 
v_key_2481_ = lean_ctor_get(v_x_2480_, 0);
v_value_2482_ = lean_ctor_get(v_x_2480_, 1);
v_tail_2483_ = lean_ctor_get(v_x_2480_, 2);
v_isSharedCheck_2506_ = !lean_is_exclusive(v_x_2480_);
if (v_isSharedCheck_2506_ == 0)
{
v___x_2485_ = v_x_2480_;
v_isShared_2486_ = v_isSharedCheck_2506_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_tail_2483_);
lean_inc(v_value_2482_);
lean_inc(v_key_2481_);
lean_dec(v_x_2480_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2506_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
lean_object* v___x_2487_; uint64_t v___x_2488_; uint64_t v___x_2489_; uint64_t v___x_2490_; uint64_t v_fold_2491_; uint64_t v___x_2492_; uint64_t v___x_2493_; uint64_t v___x_2494_; size_t v___x_2495_; size_t v___x_2496_; size_t v___x_2497_; size_t v___x_2498_; size_t v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2502_; 
v___x_2487_ = lean_array_get_size(v_x_2479_);
v___x_2488_ = l_Lean_ExprStructEq_hash(v_key_2481_);
v___x_2489_ = 32ULL;
v___x_2490_ = lean_uint64_shift_right(v___x_2488_, v___x_2489_);
v_fold_2491_ = lean_uint64_xor(v___x_2488_, v___x_2490_);
v___x_2492_ = 16ULL;
v___x_2493_ = lean_uint64_shift_right(v_fold_2491_, v___x_2492_);
v___x_2494_ = lean_uint64_xor(v_fold_2491_, v___x_2493_);
v___x_2495_ = lean_uint64_to_usize(v___x_2494_);
v___x_2496_ = lean_usize_of_nat(v___x_2487_);
v___x_2497_ = ((size_t)1ULL);
v___x_2498_ = lean_usize_sub(v___x_2496_, v___x_2497_);
v___x_2499_ = lean_usize_land(v___x_2495_, v___x_2498_);
v___x_2500_ = lean_array_uget_borrowed(v_x_2479_, v___x_2499_);
lean_inc(v___x_2500_);
if (v_isShared_2486_ == 0)
{
lean_ctor_set(v___x_2485_, 2, v___x_2500_);
v___x_2502_ = v___x_2485_;
goto v_reusejp_2501_;
}
else
{
lean_object* v_reuseFailAlloc_2505_; 
v_reuseFailAlloc_2505_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2505_, 0, v_key_2481_);
lean_ctor_set(v_reuseFailAlloc_2505_, 1, v_value_2482_);
lean_ctor_set(v_reuseFailAlloc_2505_, 2, v___x_2500_);
v___x_2502_ = v_reuseFailAlloc_2505_;
goto v_reusejp_2501_;
}
v_reusejp_2501_:
{
lean_object* v___x_2503_; 
v___x_2503_ = lean_array_uset(v_x_2479_, v___x_2499_, v___x_2502_);
v_x_2479_ = v___x_2503_;
v_x_2480_ = v_tail_2483_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19_spec__20___redArg(lean_object* v_i_2507_, lean_object* v_source_2508_, lean_object* v_target_2509_){
_start:
{
lean_object* v___x_2510_; uint8_t v___x_2511_; 
v___x_2510_ = lean_array_get_size(v_source_2508_);
v___x_2511_ = lean_nat_dec_lt(v_i_2507_, v___x_2510_);
if (v___x_2511_ == 0)
{
lean_dec_ref(v_source_2508_);
lean_dec(v_i_2507_);
return v_target_2509_;
}
else
{
lean_object* v_es_2512_; lean_object* v___x_2513_; lean_object* v_source_2514_; lean_object* v_target_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; 
v_es_2512_ = lean_array_fget(v_source_2508_, v_i_2507_);
v___x_2513_ = lean_box(0);
v_source_2514_ = lean_array_fset(v_source_2508_, v_i_2507_, v___x_2513_);
v_target_2515_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19_spec__20_spec__21___redArg(v_target_2509_, v_es_2512_);
v___x_2516_ = lean_unsigned_to_nat(1u);
v___x_2517_ = lean_nat_add(v_i_2507_, v___x_2516_);
lean_dec(v_i_2507_);
v_i_2507_ = v___x_2517_;
v_source_2508_ = v_source_2514_;
v_target_2509_ = v_target_2515_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19___redArg(lean_object* v_data_2519_){
_start:
{
lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v_nbuckets_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; 
v___x_2520_ = lean_array_get_size(v_data_2519_);
v___x_2521_ = lean_unsigned_to_nat(2u);
v_nbuckets_2522_ = lean_nat_mul(v___x_2520_, v___x_2521_);
v___x_2523_ = lean_unsigned_to_nat(0u);
v___x_2524_ = lean_box(0);
v___x_2525_ = lean_mk_array(v_nbuckets_2522_, v___x_2524_);
v___x_2526_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19_spec__20___redArg(v___x_2523_, v_data_2519_, v___x_2525_);
return v___x_2526_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13___redArg(lean_object* v_m_2527_, lean_object* v_a_2528_, lean_object* v_b_2529_){
_start:
{
lean_object* v_size_2530_; lean_object* v_buckets_2531_; lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2574_; 
v_size_2530_ = lean_ctor_get(v_m_2527_, 0);
v_buckets_2531_ = lean_ctor_get(v_m_2527_, 1);
v_isSharedCheck_2574_ = !lean_is_exclusive(v_m_2527_);
if (v_isSharedCheck_2574_ == 0)
{
v___x_2533_ = v_m_2527_;
v_isShared_2534_ = v_isSharedCheck_2574_;
goto v_resetjp_2532_;
}
else
{
lean_inc(v_buckets_2531_);
lean_inc(v_size_2530_);
lean_dec(v_m_2527_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2574_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
lean_object* v___x_2535_; uint64_t v___x_2536_; uint64_t v___x_2537_; uint64_t v___x_2538_; uint64_t v_fold_2539_; uint64_t v___x_2540_; uint64_t v___x_2541_; uint64_t v___x_2542_; size_t v___x_2543_; size_t v___x_2544_; size_t v___x_2545_; size_t v___x_2546_; size_t v___x_2547_; lean_object* v_bkt_2548_; uint8_t v___x_2549_; 
v___x_2535_ = lean_array_get_size(v_buckets_2531_);
v___x_2536_ = l_Lean_ExprStructEq_hash(v_a_2528_);
v___x_2537_ = 32ULL;
v___x_2538_ = lean_uint64_shift_right(v___x_2536_, v___x_2537_);
v_fold_2539_ = lean_uint64_xor(v___x_2536_, v___x_2538_);
v___x_2540_ = 16ULL;
v___x_2541_ = lean_uint64_shift_right(v_fold_2539_, v___x_2540_);
v___x_2542_ = lean_uint64_xor(v_fold_2539_, v___x_2541_);
v___x_2543_ = lean_uint64_to_usize(v___x_2542_);
v___x_2544_ = lean_usize_of_nat(v___x_2535_);
v___x_2545_ = ((size_t)1ULL);
v___x_2546_ = lean_usize_sub(v___x_2544_, v___x_2545_);
v___x_2547_ = lean_usize_land(v___x_2543_, v___x_2546_);
v_bkt_2548_ = lean_array_uget_borrowed(v_buckets_2531_, v___x_2547_);
v___x_2549_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18___redArg(v_a_2528_, v_bkt_2548_);
if (v___x_2549_ == 0)
{
lean_object* v___x_2550_; lean_object* v_size_x27_2551_; lean_object* v___x_2552_; lean_object* v_buckets_x27_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; uint8_t v___x_2559_; 
v___x_2550_ = lean_unsigned_to_nat(1u);
v_size_x27_2551_ = lean_nat_add(v_size_2530_, v___x_2550_);
lean_dec(v_size_2530_);
lean_inc(v_bkt_2548_);
v___x_2552_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2552_, 0, v_a_2528_);
lean_ctor_set(v___x_2552_, 1, v_b_2529_);
lean_ctor_set(v___x_2552_, 2, v_bkt_2548_);
v_buckets_x27_2553_ = lean_array_uset(v_buckets_2531_, v___x_2547_, v___x_2552_);
v___x_2554_ = lean_unsigned_to_nat(4u);
v___x_2555_ = lean_nat_mul(v_size_x27_2551_, v___x_2554_);
v___x_2556_ = lean_unsigned_to_nat(3u);
v___x_2557_ = lean_nat_div(v___x_2555_, v___x_2556_);
lean_dec(v___x_2555_);
v___x_2558_ = lean_array_get_size(v_buckets_x27_2553_);
v___x_2559_ = lean_nat_dec_le(v___x_2557_, v___x_2558_);
lean_dec(v___x_2557_);
if (v___x_2559_ == 0)
{
lean_object* v_val_2560_; lean_object* v___x_2562_; 
v_val_2560_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19___redArg(v_buckets_x27_2553_);
if (v_isShared_2534_ == 0)
{
lean_ctor_set(v___x_2533_, 1, v_val_2560_);
lean_ctor_set(v___x_2533_, 0, v_size_x27_2551_);
v___x_2562_ = v___x_2533_;
goto v_reusejp_2561_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v_size_x27_2551_);
lean_ctor_set(v_reuseFailAlloc_2563_, 1, v_val_2560_);
v___x_2562_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2561_;
}
v_reusejp_2561_:
{
return v___x_2562_;
}
}
else
{
lean_object* v___x_2565_; 
if (v_isShared_2534_ == 0)
{
lean_ctor_set(v___x_2533_, 1, v_buckets_x27_2553_);
lean_ctor_set(v___x_2533_, 0, v_size_x27_2551_);
v___x_2565_ = v___x_2533_;
goto v_reusejp_2564_;
}
else
{
lean_object* v_reuseFailAlloc_2566_; 
v_reuseFailAlloc_2566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2566_, 0, v_size_x27_2551_);
lean_ctor_set(v_reuseFailAlloc_2566_, 1, v_buckets_x27_2553_);
v___x_2565_ = v_reuseFailAlloc_2566_;
goto v_reusejp_2564_;
}
v_reusejp_2564_:
{
return v___x_2565_;
}
}
}
else
{
lean_object* v___x_2567_; lean_object* v_buckets_x27_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2572_; 
lean_inc(v_bkt_2548_);
v___x_2567_ = lean_box(0);
v_buckets_x27_2568_ = lean_array_uset(v_buckets_2531_, v___x_2547_, v___x_2567_);
v___x_2569_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__20___redArg(v_a_2528_, v_b_2529_, v_bkt_2548_);
v___x_2570_ = lean_array_uset(v_buckets_x27_2568_, v___x_2547_, v___x_2569_);
if (v_isShared_2534_ == 0)
{
lean_ctor_set(v___x_2533_, 1, v___x_2570_);
v___x_2572_ = v___x_2533_;
goto v_reusejp_2571_;
}
else
{
lean_object* v_reuseFailAlloc_2573_; 
v_reuseFailAlloc_2573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2573_, 0, v_size_2530_);
lean_ctor_set(v_reuseFailAlloc_2573_, 1, v___x_2570_);
v___x_2572_ = v_reuseFailAlloc_2573_;
goto v_reusejp_2571_;
}
v_reusejp_2571_:
{
return v___x_2572_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__2(lean_object* v_a_2575_, lean_object* v_e_2576_, lean_object* v_a_2577_){
_start:
{
lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; 
v___x_2579_ = lean_st_ref_take(v_a_2575_);
v___x_2580_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13___redArg(v___x_2579_, v_e_2576_, v_a_2577_);
v___x_2581_ = lean_st_ref_set(v_a_2575_, v___x_2580_);
v___x_2582_ = lean_box(0);
return v___x_2582_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__2___boxed(lean_object* v_a_2583_, lean_object* v_e_2584_, lean_object* v_a_2585_, lean_object* v___y_2586_){
_start:
{
lean_object* v_res_2587_; 
v_res_2587_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__2(v_a_2583_, v_e_2584_, v_a_2585_);
lean_dec(v_a_2583_);
return v_res_2587_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9___lam__0(lean_object* v_fvars_2590_, lean_object* v_pre_2591_, lean_object* v_post_2592_, uint8_t v_usedLetOnly_2593_, uint8_t v_skipConstInApp_2594_, uint8_t v_skipInstances_2595_, lean_object* v_body_2596_, lean_object* v_x_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_){
_start:
{
lean_object* v___x_2604_; lean_object* v___x_2605_; 
v___x_2604_ = lean_array_push(v_fvars_2590_, v_x_2597_);
v___x_2605_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9(v_pre_2591_, v_post_2592_, v_usedLetOnly_2593_, v_skipConstInApp_2594_, v_skipInstances_2595_, v___x_2604_, v_body_2596_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_);
return v___x_2605_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9___lam__0___boxed(lean_object* v_fvars_2606_, lean_object* v_pre_2607_, lean_object* v_post_2608_, lean_object* v_usedLetOnly_2609_, lean_object* v_skipConstInApp_2610_, lean_object* v_skipInstances_2611_, lean_object* v_body_2612_, lean_object* v_x_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_){
_start:
{
uint8_t v_usedLetOnly_boxed_2620_; uint8_t v_skipConstInApp_boxed_2621_; uint8_t v_skipInstances_boxed_2622_; lean_object* v_res_2623_; 
v_usedLetOnly_boxed_2620_ = lean_unbox(v_usedLetOnly_2609_);
v_skipConstInApp_boxed_2621_ = lean_unbox(v_skipConstInApp_2610_);
v_skipInstances_boxed_2622_ = lean_unbox(v_skipInstances_2611_);
v_res_2623_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9___lam__0(v_fvars_2606_, v_pre_2607_, v_post_2608_, v_usedLetOnly_boxed_2620_, v_skipConstInApp_boxed_2621_, v_skipInstances_boxed_2622_, v_body_2612_, v_x_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_);
lean_dec(v___y_2618_);
lean_dec_ref(v___y_2617_);
lean_dec(v___y_2616_);
lean_dec_ref(v___y_2615_);
lean_dec(v___y_2614_);
return v_res_2623_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(lean_object* v_pre_2624_, lean_object* v_post_2625_, uint8_t v_usedLetOnly_2626_, uint8_t v_skipConstInApp_2627_, uint8_t v_skipInstances_2628_, lean_object* v_e_2629_, lean_object* v_a_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_){
_start:
{
lean_object* v___x_2636_; 
lean_inc_ref(v_post_2625_);
lean_inc(v___y_2634_);
lean_inc_ref(v___y_2633_);
lean_inc(v___y_2632_);
lean_inc_ref(v___y_2631_);
lean_inc_ref(v_e_2629_);
v___x_2636_ = lean_apply_6(v_post_2625_, v_e_2629_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_, lean_box(0));
if (lean_obj_tag(v___x_2636_) == 0)
{
lean_object* v_a_2637_; lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2655_; 
v_a_2637_ = lean_ctor_get(v___x_2636_, 0);
v_isSharedCheck_2655_ = !lean_is_exclusive(v___x_2636_);
if (v_isSharedCheck_2655_ == 0)
{
v___x_2639_ = v___x_2636_;
v_isShared_2640_ = v_isSharedCheck_2655_;
goto v_resetjp_2638_;
}
else
{
lean_inc(v_a_2637_);
lean_dec(v___x_2636_);
v___x_2639_ = lean_box(0);
v_isShared_2640_ = v_isSharedCheck_2655_;
goto v_resetjp_2638_;
}
v_resetjp_2638_:
{
switch(lean_obj_tag(v_a_2637_))
{
case 0:
{
lean_object* v_e_2641_; lean_object* v___x_2643_; 
lean_dec_ref(v_e_2629_);
lean_dec_ref(v_post_2625_);
lean_dec_ref(v_pre_2624_);
v_e_2641_ = lean_ctor_get(v_a_2637_, 0);
lean_inc_ref(v_e_2641_);
lean_dec_ref(v_a_2637_);
if (v_isShared_2640_ == 0)
{
lean_ctor_set(v___x_2639_, 0, v_e_2641_);
v___x_2643_ = v___x_2639_;
goto v_reusejp_2642_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v_e_2641_);
v___x_2643_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2642_;
}
v_reusejp_2642_:
{
return v___x_2643_;
}
}
case 1:
{
lean_object* v_e_2645_; lean_object* v___x_2646_; 
lean_del_object(v___x_2639_);
lean_dec_ref(v_e_2629_);
v_e_2645_ = lean_ctor_get(v_a_2637_, 0);
lean_inc_ref(v_e_2645_);
lean_dec_ref(v_a_2637_);
v___x_2646_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2624_, v_post_2625_, v_usedLetOnly_2626_, v_skipConstInApp_2627_, v_skipInstances_2628_, v_e_2645_, v_a_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_);
return v___x_2646_;
}
default: 
{
lean_object* v_e_x3f_2647_; 
lean_dec_ref(v_post_2625_);
lean_dec_ref(v_pre_2624_);
v_e_x3f_2647_ = lean_ctor_get(v_a_2637_, 0);
lean_inc(v_e_x3f_2647_);
lean_dec_ref(v_a_2637_);
if (lean_obj_tag(v_e_x3f_2647_) == 0)
{
lean_object* v___x_2649_; 
if (v_isShared_2640_ == 0)
{
lean_ctor_set(v___x_2639_, 0, v_e_2629_);
v___x_2649_ = v___x_2639_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v_e_2629_);
v___x_2649_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
return v___x_2649_;
}
}
else
{
lean_object* v_val_2651_; lean_object* v___x_2653_; 
lean_dec_ref(v_e_2629_);
v_val_2651_ = lean_ctor_get(v_e_x3f_2647_, 0);
lean_inc(v_val_2651_);
lean_dec_ref(v_e_x3f_2647_);
if (v_isShared_2640_ == 0)
{
lean_ctor_set(v___x_2639_, 0, v_val_2651_);
v___x_2653_ = v___x_2639_;
goto v_reusejp_2652_;
}
else
{
lean_object* v_reuseFailAlloc_2654_; 
v_reuseFailAlloc_2654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2654_, 0, v_val_2651_);
v___x_2653_ = v_reuseFailAlloc_2654_;
goto v_reusejp_2652_;
}
v_reusejp_2652_:
{
return v___x_2653_;
}
}
}
}
}
}
else
{
lean_object* v_a_2656_; lean_object* v___x_2658_; uint8_t v_isShared_2659_; uint8_t v_isSharedCheck_2663_; 
lean_dec_ref(v_e_2629_);
lean_dec_ref(v_post_2625_);
lean_dec_ref(v_pre_2624_);
v_a_2656_ = lean_ctor_get(v___x_2636_, 0);
v_isSharedCheck_2663_ = !lean_is_exclusive(v___x_2636_);
if (v_isSharedCheck_2663_ == 0)
{
v___x_2658_ = v___x_2636_;
v_isShared_2659_ = v_isSharedCheck_2663_;
goto v_resetjp_2657_;
}
else
{
lean_inc(v_a_2656_);
lean_dec(v___x_2636_);
v___x_2658_ = lean_box(0);
v_isShared_2659_ = v_isSharedCheck_2663_;
goto v_resetjp_2657_;
}
v_resetjp_2657_:
{
lean_object* v___x_2661_; 
if (v_isShared_2659_ == 0)
{
v___x_2661_ = v___x_2658_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2662_; 
v_reuseFailAlloc_2662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2662_, 0, v_a_2656_);
v___x_2661_ = v_reuseFailAlloc_2662_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
return v___x_2661_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9(lean_object* v_pre_2664_, lean_object* v_post_2665_, uint8_t v_usedLetOnly_2666_, uint8_t v_skipConstInApp_2667_, uint8_t v_skipInstances_2668_, lean_object* v_fvars_2669_, lean_object* v_e_2670_, lean_object* v_a_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_){
_start:
{
if (lean_obj_tag(v_e_2670_) == 6)
{
lean_object* v_binderName_2677_; lean_object* v_binderType_2678_; lean_object* v_body_2679_; uint8_t v_binderInfo_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; 
v_binderName_2677_ = lean_ctor_get(v_e_2670_, 0);
lean_inc(v_binderName_2677_);
v_binderType_2678_ = lean_ctor_get(v_e_2670_, 1);
lean_inc_ref(v_binderType_2678_);
v_body_2679_ = lean_ctor_get(v_e_2670_, 2);
lean_inc_ref(v_body_2679_);
v_binderInfo_2680_ = lean_ctor_get_uint8(v_e_2670_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_2670_);
v___x_2681_ = lean_expr_instantiate_rev(v_binderType_2678_, v_fvars_2669_);
lean_dec_ref(v_binderType_2678_);
lean_inc_ref(v_post_2665_);
lean_inc_ref(v_pre_2664_);
v___x_2682_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2664_, v_post_2665_, v_usedLetOnly_2666_, v_skipConstInApp_2667_, v_skipInstances_2668_, v___x_2681_, v_a_2671_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_);
if (lean_obj_tag(v___x_2682_) == 0)
{
lean_object* v_a_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___f_2687_; uint8_t v___x_2688_; lean_object* v___x_2689_; 
v_a_2683_ = lean_ctor_get(v___x_2682_, 0);
lean_inc(v_a_2683_);
lean_dec_ref(v___x_2682_);
v___x_2684_ = lean_box(v_usedLetOnly_2666_);
v___x_2685_ = lean_box(v_skipConstInApp_2667_);
v___x_2686_ = lean_box(v_skipInstances_2668_);
v___f_2687_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9___lam__0___boxed), 14, 7);
lean_closure_set(v___f_2687_, 0, v_fvars_2669_);
lean_closure_set(v___f_2687_, 1, v_pre_2664_);
lean_closure_set(v___f_2687_, 2, v_post_2665_);
lean_closure_set(v___f_2687_, 3, v___x_2684_);
lean_closure_set(v___f_2687_, 4, v___x_2685_);
lean_closure_set(v___f_2687_, 5, v___x_2686_);
lean_closure_set(v___f_2687_, 6, v_body_2679_);
v___x_2688_ = 0;
v___x_2689_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg(v_binderName_2677_, v_binderInfo_2680_, v_a_2683_, v___f_2687_, v___x_2688_, v_a_2671_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_);
return v___x_2689_;
}
else
{
lean_dec_ref(v_body_2679_);
lean_dec(v_binderName_2677_);
lean_dec_ref(v_fvars_2669_);
lean_dec_ref(v_post_2665_);
lean_dec_ref(v_pre_2664_);
return v___x_2682_;
}
}
else
{
lean_object* v___x_2690_; lean_object* v___x_2691_; 
v___x_2690_ = lean_expr_instantiate_rev(v_e_2670_, v_fvars_2669_);
lean_dec_ref(v_e_2670_);
lean_inc_ref(v_post_2665_);
lean_inc_ref(v_pre_2664_);
v___x_2691_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2664_, v_post_2665_, v_usedLetOnly_2666_, v_skipConstInApp_2667_, v_skipInstances_2668_, v___x_2690_, v_a_2671_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_);
if (lean_obj_tag(v___x_2691_) == 0)
{
lean_object* v_a_2692_; uint8_t v___x_2693_; uint8_t v___x_2694_; uint8_t v___x_2695_; lean_object* v___x_2696_; 
v_a_2692_ = lean_ctor_get(v___x_2691_, 0);
lean_inc(v_a_2692_);
lean_dec_ref(v___x_2691_);
v___x_2693_ = 0;
v___x_2694_ = 1;
v___x_2695_ = 1;
v___x_2696_ = l_Lean_Meta_mkLambdaFVars(v_fvars_2669_, v_a_2692_, v___x_2693_, v_usedLetOnly_2666_, v___x_2693_, v___x_2694_, v___x_2695_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_);
lean_dec_ref(v_fvars_2669_);
if (lean_obj_tag(v___x_2696_) == 0)
{
lean_object* v_a_2697_; lean_object* v___x_2698_; 
v_a_2697_ = lean_ctor_get(v___x_2696_, 0);
lean_inc(v_a_2697_);
lean_dec_ref(v___x_2696_);
v___x_2698_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_2664_, v_post_2665_, v_usedLetOnly_2666_, v_skipConstInApp_2667_, v_skipInstances_2668_, v_a_2697_, v_a_2671_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_);
return v___x_2698_;
}
else
{
lean_dec_ref(v_post_2665_);
lean_dec_ref(v_pre_2664_);
return v___x_2696_;
}
}
else
{
lean_dec_ref(v_fvars_2669_);
lean_dec_ref(v_post_2665_);
lean_dec_ref(v_pre_2664_);
return v___x_2691_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10___lam__0(lean_object* v_fvars_2699_, lean_object* v_pre_2700_, lean_object* v_post_2701_, uint8_t v_usedLetOnly_2702_, uint8_t v_skipConstInApp_2703_, uint8_t v_skipInstances_2704_, lean_object* v_body_2705_, lean_object* v_x_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_){
_start:
{
lean_object* v___x_2713_; lean_object* v___x_2714_; 
v___x_2713_ = lean_array_push(v_fvars_2699_, v_x_2706_);
v___x_2714_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10(v_pre_2700_, v_post_2701_, v_usedLetOnly_2702_, v_skipConstInApp_2703_, v_skipInstances_2704_, v___x_2713_, v_body_2705_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_);
return v___x_2714_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10___lam__0___boxed(lean_object* v_fvars_2715_, lean_object* v_pre_2716_, lean_object* v_post_2717_, lean_object* v_usedLetOnly_2718_, lean_object* v_skipConstInApp_2719_, lean_object* v_skipInstances_2720_, lean_object* v_body_2721_, lean_object* v_x_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_){
_start:
{
uint8_t v_usedLetOnly_boxed_2729_; uint8_t v_skipConstInApp_boxed_2730_; uint8_t v_skipInstances_boxed_2731_; lean_object* v_res_2732_; 
v_usedLetOnly_boxed_2729_ = lean_unbox(v_usedLetOnly_2718_);
v_skipConstInApp_boxed_2730_ = lean_unbox(v_skipConstInApp_2719_);
v_skipInstances_boxed_2731_ = lean_unbox(v_skipInstances_2720_);
v_res_2732_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10___lam__0(v_fvars_2715_, v_pre_2716_, v_post_2717_, v_usedLetOnly_boxed_2729_, v_skipConstInApp_boxed_2730_, v_skipInstances_boxed_2731_, v_body_2721_, v_x_2722_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_);
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec(v___y_2725_);
lean_dec_ref(v___y_2724_);
lean_dec(v___y_2723_);
return v_res_2732_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10(lean_object* v_pre_2733_, lean_object* v_post_2734_, uint8_t v_usedLetOnly_2735_, uint8_t v_skipConstInApp_2736_, uint8_t v_skipInstances_2737_, lean_object* v_fvars_2738_, lean_object* v_e_2739_, lean_object* v_a_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_){
_start:
{
if (lean_obj_tag(v_e_2739_) == 8)
{
lean_object* v_declName_2746_; lean_object* v_type_2747_; lean_object* v_value_2748_; lean_object* v_body_2749_; uint8_t v_nondep_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; 
v_declName_2746_ = lean_ctor_get(v_e_2739_, 0);
lean_inc(v_declName_2746_);
v_type_2747_ = lean_ctor_get(v_e_2739_, 1);
lean_inc_ref(v_type_2747_);
v_value_2748_ = lean_ctor_get(v_e_2739_, 2);
lean_inc_ref(v_value_2748_);
v_body_2749_ = lean_ctor_get(v_e_2739_, 3);
lean_inc_ref(v_body_2749_);
v_nondep_2750_ = lean_ctor_get_uint8(v_e_2739_, sizeof(void*)*4 + 8);
lean_dec_ref(v_e_2739_);
v___x_2751_ = lean_expr_instantiate_rev(v_type_2747_, v_fvars_2738_);
lean_dec_ref(v_type_2747_);
lean_inc_ref(v_post_2734_);
lean_inc_ref(v_pre_2733_);
v___x_2752_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2733_, v_post_2734_, v_usedLetOnly_2735_, v_skipConstInApp_2736_, v_skipInstances_2737_, v___x_2751_, v_a_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_);
if (lean_obj_tag(v___x_2752_) == 0)
{
lean_object* v_a_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; 
v_a_2753_ = lean_ctor_get(v___x_2752_, 0);
lean_inc(v_a_2753_);
lean_dec_ref(v___x_2752_);
v___x_2754_ = lean_expr_instantiate_rev(v_value_2748_, v_fvars_2738_);
lean_dec_ref(v_value_2748_);
lean_inc_ref(v_post_2734_);
lean_inc_ref(v_pre_2733_);
v___x_2755_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2733_, v_post_2734_, v_usedLetOnly_2735_, v_skipConstInApp_2736_, v_skipInstances_2737_, v___x_2754_, v_a_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_);
if (lean_obj_tag(v___x_2755_) == 0)
{
lean_object* v_a_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___f_2760_; uint8_t v___x_2761_; lean_object* v___x_2762_; 
v_a_2756_ = lean_ctor_get(v___x_2755_, 0);
lean_inc(v_a_2756_);
lean_dec_ref(v___x_2755_);
v___x_2757_ = lean_box(v_usedLetOnly_2735_);
v___x_2758_ = lean_box(v_skipConstInApp_2736_);
v___x_2759_ = lean_box(v_skipInstances_2737_);
v___f_2760_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10___lam__0___boxed), 14, 7);
lean_closure_set(v___f_2760_, 0, v_fvars_2738_);
lean_closure_set(v___f_2760_, 1, v_pre_2733_);
lean_closure_set(v___f_2760_, 2, v_post_2734_);
lean_closure_set(v___f_2760_, 3, v___x_2757_);
lean_closure_set(v___f_2760_, 4, v___x_2758_);
lean_closure_set(v___f_2760_, 5, v___x_2759_);
lean_closure_set(v___f_2760_, 6, v_body_2749_);
v___x_2761_ = 0;
v___x_2762_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13___redArg(v_declName_2746_, v_a_2753_, v_a_2756_, v___f_2760_, v_nondep_2750_, v___x_2761_, v_a_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_);
return v___x_2762_;
}
else
{
lean_dec(v_a_2753_);
lean_dec_ref(v_body_2749_);
lean_dec(v_declName_2746_);
lean_dec_ref(v_fvars_2738_);
lean_dec_ref(v_post_2734_);
lean_dec_ref(v_pre_2733_);
return v___x_2755_;
}
}
else
{
lean_dec_ref(v_body_2749_);
lean_dec_ref(v_value_2748_);
lean_dec(v_declName_2746_);
lean_dec_ref(v_fvars_2738_);
lean_dec_ref(v_post_2734_);
lean_dec_ref(v_pre_2733_);
return v___x_2752_;
}
}
else
{
lean_object* v___x_2763_; lean_object* v___x_2764_; 
v___x_2763_ = lean_expr_instantiate_rev(v_e_2739_, v_fvars_2738_);
lean_dec_ref(v_e_2739_);
lean_inc_ref(v_post_2734_);
lean_inc_ref(v_pre_2733_);
v___x_2764_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2733_, v_post_2734_, v_usedLetOnly_2735_, v_skipConstInApp_2736_, v_skipInstances_2737_, v___x_2763_, v_a_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_);
if (lean_obj_tag(v___x_2764_) == 0)
{
lean_object* v_a_2765_; uint8_t v___x_2766_; uint8_t v___x_2767_; lean_object* v___x_2768_; 
v_a_2765_ = lean_ctor_get(v___x_2764_, 0);
lean_inc(v_a_2765_);
lean_dec_ref(v___x_2764_);
v___x_2766_ = 0;
v___x_2767_ = 1;
v___x_2768_ = l_Lean_Meta_mkLetFVars(v_fvars_2738_, v_a_2765_, v_usedLetOnly_2735_, v___x_2766_, v___x_2767_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_);
lean_dec_ref(v_fvars_2738_);
if (lean_obj_tag(v___x_2768_) == 0)
{
lean_object* v_a_2769_; lean_object* v___x_2770_; 
v_a_2769_ = lean_ctor_get(v___x_2768_, 0);
lean_inc(v_a_2769_);
lean_dec_ref(v___x_2768_);
v___x_2770_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_2733_, v_post_2734_, v_usedLetOnly_2735_, v_skipConstInApp_2736_, v_skipInstances_2737_, v_a_2769_, v_a_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_);
return v___x_2770_;
}
else
{
lean_dec_ref(v_post_2734_);
lean_dec_ref(v_pre_2733_);
return v___x_2768_;
}
}
else
{
lean_dec_ref(v_fvars_2738_);
lean_dec_ref(v_post_2734_);
lean_dec_ref(v_pre_2733_);
return v___x_2764_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__4(lean_object* v_pre_2771_, lean_object* v_post_2772_, uint8_t v_usedLetOnly_2773_, uint8_t v_skipConstInApp_2774_, uint8_t v_skipInstances_2775_, size_t v_sz_2776_, size_t v_i_2777_, lean_object* v_bs_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_){
_start:
{
uint8_t v___x_2785_; 
v___x_2785_ = lean_usize_dec_lt(v_i_2777_, v_sz_2776_);
if (v___x_2785_ == 0)
{
lean_object* v___x_2786_; 
lean_dec_ref(v_post_2772_);
lean_dec_ref(v_pre_2771_);
v___x_2786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2786_, 0, v_bs_2778_);
return v___x_2786_;
}
else
{
lean_object* v_v_2787_; lean_object* v___x_2788_; 
v_v_2787_ = lean_array_uget_borrowed(v_bs_2778_, v_i_2777_);
lean_inc(v_v_2787_);
lean_inc_ref(v_post_2772_);
lean_inc_ref(v_pre_2771_);
v___x_2788_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2771_, v_post_2772_, v_usedLetOnly_2773_, v_skipConstInApp_2774_, v_skipInstances_2775_, v_v_2787_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_);
if (lean_obj_tag(v___x_2788_) == 0)
{
lean_object* v_a_2789_; lean_object* v___x_2790_; lean_object* v_bs_x27_2791_; size_t v___x_2792_; size_t v___x_2793_; lean_object* v___x_2794_; 
v_a_2789_ = lean_ctor_get(v___x_2788_, 0);
lean_inc(v_a_2789_);
lean_dec_ref(v___x_2788_);
v___x_2790_ = lean_unsigned_to_nat(0u);
v_bs_x27_2791_ = lean_array_uset(v_bs_2778_, v_i_2777_, v___x_2790_);
v___x_2792_ = ((size_t)1ULL);
v___x_2793_ = lean_usize_add(v_i_2777_, v___x_2792_);
v___x_2794_ = lean_array_uset(v_bs_x27_2791_, v_i_2777_, v_a_2789_);
v_i_2777_ = v___x_2793_;
v_bs_2778_ = v___x_2794_;
goto _start;
}
else
{
lean_object* v_a_2796_; lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2803_; 
lean_dec_ref(v_bs_2778_);
lean_dec_ref(v_post_2772_);
lean_dec_ref(v_pre_2771_);
v_a_2796_ = lean_ctor_get(v___x_2788_, 0);
v_isSharedCheck_2803_ = !lean_is_exclusive(v___x_2788_);
if (v_isSharedCheck_2803_ == 0)
{
v___x_2798_ = v___x_2788_;
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
else
{
lean_inc(v_a_2796_);
lean_dec(v___x_2788_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
v_resetjp_2797_:
{
lean_object* v___x_2801_; 
if (v_isShared_2799_ == 0)
{
v___x_2801_ = v___x_2798_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v_a_2796_);
v___x_2801_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
return v___x_2801_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___lam__0(lean_object* v_pre_2804_, lean_object* v_post_2805_, uint8_t v_usedLetOnly_2806_, uint8_t v_skipConstInApp_2807_, uint8_t v_skipInstances_2808_, lean_object* v___x_2809_, lean_object* v___y_2810_, lean_object* v_b_2811_, lean_object* v_a_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_){
_start:
{
lean_object* v___x_2818_; 
v___x_2818_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2804_, v_post_2805_, v_usedLetOnly_2806_, v_skipConstInApp_2807_, v_skipInstances_2808_, v___x_2809_, v___y_2810_, v___y_2813_, v___y_2814_, v___y_2815_, v___y_2816_);
if (lean_obj_tag(v___x_2818_) == 0)
{
lean_object* v_a_2819_; lean_object* v___x_2821_; uint8_t v_isShared_2822_; uint8_t v_isSharedCheck_2828_; 
v_a_2819_ = lean_ctor_get(v___x_2818_, 0);
v_isSharedCheck_2828_ = !lean_is_exclusive(v___x_2818_);
if (v_isSharedCheck_2828_ == 0)
{
v___x_2821_ = v___x_2818_;
v_isShared_2822_ = v_isSharedCheck_2828_;
goto v_resetjp_2820_;
}
else
{
lean_inc(v_a_2819_);
lean_dec(v___x_2818_);
v___x_2821_ = lean_box(0);
v_isShared_2822_ = v_isSharedCheck_2828_;
goto v_resetjp_2820_;
}
v_resetjp_2820_:
{
lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2826_; 
v___x_2823_ = lean_array_fset(v_b_2811_, v_a_2812_, v_a_2819_);
v___x_2824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2824_, 0, v___x_2823_);
if (v_isShared_2822_ == 0)
{
lean_ctor_set(v___x_2821_, 0, v___x_2824_);
v___x_2826_ = v___x_2821_;
goto v_reusejp_2825_;
}
else
{
lean_object* v_reuseFailAlloc_2827_; 
v_reuseFailAlloc_2827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2827_, 0, v___x_2824_);
v___x_2826_ = v_reuseFailAlloc_2827_;
goto v_reusejp_2825_;
}
v_reusejp_2825_:
{
return v___x_2826_;
}
}
}
else
{
lean_object* v_a_2829_; lean_object* v___x_2831_; uint8_t v_isShared_2832_; uint8_t v_isSharedCheck_2836_; 
lean_dec_ref(v_b_2811_);
v_a_2829_ = lean_ctor_get(v___x_2818_, 0);
v_isSharedCheck_2836_ = !lean_is_exclusive(v___x_2818_);
if (v_isSharedCheck_2836_ == 0)
{
v___x_2831_ = v___x_2818_;
v_isShared_2832_ = v_isSharedCheck_2836_;
goto v_resetjp_2830_;
}
else
{
lean_inc(v_a_2829_);
lean_dec(v___x_2818_);
v___x_2831_ = lean_box(0);
v_isShared_2832_ = v_isSharedCheck_2836_;
goto v_resetjp_2830_;
}
v_resetjp_2830_:
{
lean_object* v___x_2834_; 
if (v_isShared_2832_ == 0)
{
v___x_2834_ = v___x_2831_;
goto v_reusejp_2833_;
}
else
{
lean_object* v_reuseFailAlloc_2835_; 
v_reuseFailAlloc_2835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2835_, 0, v_a_2829_);
v___x_2834_ = v_reuseFailAlloc_2835_;
goto v_reusejp_2833_;
}
v_reusejp_2833_:
{
return v___x_2834_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___lam__0___boxed(lean_object* v_pre_2837_, lean_object* v_post_2838_, lean_object* v_usedLetOnly_2839_, lean_object* v_skipConstInApp_2840_, lean_object* v_skipInstances_2841_, lean_object* v___x_2842_, lean_object* v___y_2843_, lean_object* v_b_2844_, lean_object* v_a_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_){
_start:
{
uint8_t v_usedLetOnly_boxed_2851_; uint8_t v_skipConstInApp_boxed_2852_; uint8_t v_skipInstances_boxed_2853_; lean_object* v_res_2854_; 
v_usedLetOnly_boxed_2851_ = lean_unbox(v_usedLetOnly_2839_);
v_skipConstInApp_boxed_2852_ = lean_unbox(v_skipConstInApp_2840_);
v_skipInstances_boxed_2853_ = lean_unbox(v_skipInstances_2841_);
v_res_2854_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___lam__0(v_pre_2837_, v_post_2838_, v_usedLetOnly_boxed_2851_, v_skipConstInApp_boxed_2852_, v_skipInstances_boxed_2853_, v___x_2842_, v___y_2843_, v_b_2844_, v_a_2845_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_);
lean_dec(v___y_2849_);
lean_dec_ref(v___y_2848_);
lean_dec(v___y_2847_);
lean_dec_ref(v___y_2846_);
lean_dec(v_a_2845_);
lean_dec(v___y_2843_);
return v_res_2854_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg(lean_object* v_upperBound_2855_, lean_object* v___x_2856_, lean_object* v_pre_2857_, lean_object* v_post_2858_, uint8_t v_usedLetOnly_2859_, uint8_t v_skipConstInApp_2860_, uint8_t v_skipInstances_2861_, lean_object* v_a_2862_, lean_object* v_b_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_){
_start:
{
lean_object* v___y_2871_; uint8_t v___x_2894_; 
v___x_2894_ = lean_nat_dec_lt(v_a_2862_, v_upperBound_2855_);
if (v___x_2894_ == 0)
{
lean_object* v___x_2895_; 
lean_dec(v_a_2862_);
lean_dec_ref(v_post_2858_);
lean_dec_ref(v_pre_2857_);
v___x_2895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2895_, 0, v_b_2863_);
return v___x_2895_;
}
else
{
lean_object* v___x_2896_; lean_object* v___x_2897_; uint8_t v___x_2898_; 
v___x_2896_ = lean_array_fget_borrowed(v_b_2863_, v_a_2862_);
v___x_2897_ = lean_array_get_size(v___x_2856_);
v___x_2898_ = lean_nat_dec_lt(v_a_2862_, v___x_2897_);
if (v___x_2898_ == 0)
{
lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___f_2902_; 
lean_inc(v___x_2896_);
v___x_2899_ = lean_box(v_usedLetOnly_2859_);
v___x_2900_ = lean_box(v_skipConstInApp_2860_);
v___x_2901_ = lean_box(v_skipInstances_2861_);
lean_inc(v_a_2862_);
lean_inc(v___y_2864_);
lean_inc_ref(v_post_2858_);
lean_inc_ref(v_pre_2857_);
v___f_2902_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_2902_, 0, v_pre_2857_);
lean_closure_set(v___f_2902_, 1, v_post_2858_);
lean_closure_set(v___f_2902_, 2, v___x_2899_);
lean_closure_set(v___f_2902_, 3, v___x_2900_);
lean_closure_set(v___f_2902_, 4, v___x_2901_);
lean_closure_set(v___f_2902_, 5, v___x_2896_);
lean_closure_set(v___f_2902_, 6, v___y_2864_);
lean_closure_set(v___f_2902_, 7, v_b_2863_);
lean_closure_set(v___f_2902_, 8, v_a_2862_);
v___y_2871_ = v___f_2902_;
goto v___jp_2870_;
}
else
{
lean_object* v___x_2903_; uint8_t v_isInstance_2904_; 
v___x_2903_ = lean_array_fget_borrowed(v___x_2856_, v_a_2862_);
v_isInstance_2904_ = lean_ctor_get_uint8(v___x_2903_, sizeof(void*)*1 + 4);
if (v_isInstance_2904_ == 0)
{
lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___f_2908_; 
lean_inc(v___x_2896_);
v___x_2905_ = lean_box(v_usedLetOnly_2859_);
v___x_2906_ = lean_box(v_skipConstInApp_2860_);
v___x_2907_ = lean_box(v_skipInstances_2861_);
lean_inc(v_a_2862_);
lean_inc(v___y_2864_);
lean_inc_ref(v_post_2858_);
lean_inc_ref(v_pre_2857_);
v___f_2908_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_2908_, 0, v_pre_2857_);
lean_closure_set(v___f_2908_, 1, v_post_2858_);
lean_closure_set(v___f_2908_, 2, v___x_2905_);
lean_closure_set(v___f_2908_, 3, v___x_2906_);
lean_closure_set(v___f_2908_, 4, v___x_2907_);
lean_closure_set(v___f_2908_, 5, v___x_2896_);
lean_closure_set(v___f_2908_, 6, v___y_2864_);
lean_closure_set(v___f_2908_, 7, v_b_2863_);
lean_closure_set(v___f_2908_, 8, v_a_2862_);
v___y_2871_ = v___f_2908_;
goto v___jp_2870_;
}
else
{
lean_object* v___x_2909_; lean_object* v___f_2910_; 
v___x_2909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2909_, 0, v_b_2863_);
v___f_2910_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_2910_, 0, v___x_2909_);
v___y_2871_ = v___f_2910_;
goto v___jp_2870_;
}
}
}
v___jp_2870_:
{
lean_object* v___x_2872_; 
lean_inc(v___y_2868_);
lean_inc_ref(v___y_2867_);
lean_inc(v___y_2866_);
lean_inc_ref(v___y_2865_);
v___x_2872_ = lean_apply_5(v___y_2871_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_, lean_box(0));
if (lean_obj_tag(v___x_2872_) == 0)
{
lean_object* v_a_2873_; lean_object* v___x_2875_; uint8_t v_isShared_2876_; uint8_t v_isSharedCheck_2885_; 
v_a_2873_ = lean_ctor_get(v___x_2872_, 0);
v_isSharedCheck_2885_ = !lean_is_exclusive(v___x_2872_);
if (v_isSharedCheck_2885_ == 0)
{
v___x_2875_ = v___x_2872_;
v_isShared_2876_ = v_isSharedCheck_2885_;
goto v_resetjp_2874_;
}
else
{
lean_inc(v_a_2873_);
lean_dec(v___x_2872_);
v___x_2875_ = lean_box(0);
v_isShared_2876_ = v_isSharedCheck_2885_;
goto v_resetjp_2874_;
}
v_resetjp_2874_:
{
if (lean_obj_tag(v_a_2873_) == 0)
{
lean_object* v_a_2877_; lean_object* v___x_2879_; 
lean_dec(v_a_2862_);
lean_dec_ref(v_post_2858_);
lean_dec_ref(v_pre_2857_);
v_a_2877_ = lean_ctor_get(v_a_2873_, 0);
lean_inc(v_a_2877_);
lean_dec_ref(v_a_2873_);
if (v_isShared_2876_ == 0)
{
lean_ctor_set(v___x_2875_, 0, v_a_2877_);
v___x_2879_ = v___x_2875_;
goto v_reusejp_2878_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v_a_2877_);
v___x_2879_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2878_;
}
v_reusejp_2878_:
{
return v___x_2879_;
}
}
else
{
lean_object* v_a_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; 
lean_del_object(v___x_2875_);
v_a_2881_ = lean_ctor_get(v_a_2873_, 0);
lean_inc(v_a_2881_);
lean_dec_ref(v_a_2873_);
v___x_2882_ = lean_unsigned_to_nat(1u);
v___x_2883_ = lean_nat_add(v_a_2862_, v___x_2882_);
lean_dec(v_a_2862_);
v_a_2862_ = v___x_2883_;
v_b_2863_ = v_a_2881_;
goto _start;
}
}
}
else
{
lean_object* v_a_2886_; lean_object* v___x_2888_; uint8_t v_isShared_2889_; uint8_t v_isSharedCheck_2893_; 
lean_dec(v_a_2862_);
lean_dec_ref(v_post_2858_);
lean_dec_ref(v_pre_2857_);
v_a_2886_ = lean_ctor_get(v___x_2872_, 0);
v_isSharedCheck_2893_ = !lean_is_exclusive(v___x_2872_);
if (v_isSharedCheck_2893_ == 0)
{
v___x_2888_ = v___x_2872_;
v_isShared_2889_ = v_isSharedCheck_2893_;
goto v_resetjp_2887_;
}
else
{
lean_inc(v_a_2886_);
lean_dec(v___x_2872_);
v___x_2888_ = lean_box(0);
v_isShared_2889_ = v_isSharedCheck_2893_;
goto v_resetjp_2887_;
}
v_resetjp_2887_:
{
lean_object* v___x_2891_; 
if (v_isShared_2889_ == 0)
{
v___x_2891_ = v___x_2888_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2892_; 
v_reuseFailAlloc_2892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2892_, 0, v_a_2886_);
v___x_2891_ = v_reuseFailAlloc_2892_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
return v___x_2891_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__11(uint8_t v_skipInstances_2911_, lean_object* v_pre_2912_, lean_object* v_post_2913_, uint8_t v_usedLetOnly_2914_, uint8_t v_skipConstInApp_2915_, lean_object* v_x_2916_, lean_object* v_x_2917_, lean_object* v_x_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_){
_start:
{
lean_object* v_f_2926_; lean_object* v___y_2927_; lean_object* v___y_2928_; lean_object* v___y_2929_; lean_object* v___y_2930_; lean_object* v___y_2931_; 
if (lean_obj_tag(v_x_2916_) == 5)
{
lean_object* v_fn_2974_; lean_object* v_arg_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; 
v_fn_2974_ = lean_ctor_get(v_x_2916_, 0);
lean_inc_ref(v_fn_2974_);
v_arg_2975_ = lean_ctor_get(v_x_2916_, 1);
lean_inc_ref(v_arg_2975_);
lean_dec_ref(v_x_2916_);
v___x_2976_ = lean_array_set(v_x_2917_, v_x_2918_, v_arg_2975_);
v___x_2977_ = lean_unsigned_to_nat(1u);
v___x_2978_ = lean_nat_sub(v_x_2918_, v___x_2977_);
lean_dec(v_x_2918_);
v_x_2916_ = v_fn_2974_;
v_x_2917_ = v___x_2976_;
v_x_2918_ = v___x_2978_;
goto _start;
}
else
{
lean_dec(v_x_2918_);
if (v_skipConstInApp_2915_ == 0)
{
goto v___jp_2971_;
}
else
{
uint8_t v___x_2980_; 
v___x_2980_ = l_Lean_Expr_isConst(v_x_2916_);
if (v___x_2980_ == 0)
{
goto v___jp_2971_;
}
else
{
v_f_2926_ = v_x_2916_;
v___y_2927_ = v___y_2919_;
v___y_2928_ = v___y_2920_;
v___y_2929_ = v___y_2921_;
v___y_2930_ = v___y_2922_;
v___y_2931_ = v___y_2923_;
goto v___jp_2925_;
}
}
}
v___jp_2925_:
{
if (v_skipInstances_2911_ == 0)
{
size_t v_sz_2932_; size_t v___x_2933_; lean_object* v___x_2934_; 
v_sz_2932_ = lean_array_size(v_x_2917_);
v___x_2933_ = ((size_t)0ULL);
lean_inc_ref(v_post_2913_);
lean_inc_ref(v_pre_2912_);
v___x_2934_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__4(v_pre_2912_, v_post_2913_, v_usedLetOnly_2914_, v_skipConstInApp_2915_, v_skipInstances_2911_, v_sz_2932_, v___x_2933_, v_x_2917_, v___y_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_);
if (lean_obj_tag(v___x_2934_) == 0)
{
lean_object* v_a_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; 
v_a_2935_ = lean_ctor_get(v___x_2934_, 0);
lean_inc(v_a_2935_);
lean_dec_ref(v___x_2934_);
v___x_2936_ = l_Lean_mkAppN(v_f_2926_, v_a_2935_);
lean_dec(v_a_2935_);
v___x_2937_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_2912_, v_post_2913_, v_usedLetOnly_2914_, v_skipConstInApp_2915_, v_skipInstances_2911_, v___x_2936_, v___y_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_);
return v___x_2937_;
}
else
{
lean_object* v_a_2938_; lean_object* v___x_2940_; uint8_t v_isShared_2941_; uint8_t v_isSharedCheck_2945_; 
lean_dec_ref(v_f_2926_);
lean_dec_ref(v_post_2913_);
lean_dec_ref(v_pre_2912_);
v_a_2938_ = lean_ctor_get(v___x_2934_, 0);
v_isSharedCheck_2945_ = !lean_is_exclusive(v___x_2934_);
if (v_isSharedCheck_2945_ == 0)
{
v___x_2940_ = v___x_2934_;
v_isShared_2941_ = v_isSharedCheck_2945_;
goto v_resetjp_2939_;
}
else
{
lean_inc(v_a_2938_);
lean_dec(v___x_2934_);
v___x_2940_ = lean_box(0);
v_isShared_2941_ = v_isSharedCheck_2945_;
goto v_resetjp_2939_;
}
v_resetjp_2939_:
{
lean_object* v___x_2943_; 
if (v_isShared_2941_ == 0)
{
v___x_2943_ = v___x_2940_;
goto v_reusejp_2942_;
}
else
{
lean_object* v_reuseFailAlloc_2944_; 
v_reuseFailAlloc_2944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2944_, 0, v_a_2938_);
v___x_2943_ = v_reuseFailAlloc_2944_;
goto v_reusejp_2942_;
}
v_reusejp_2942_:
{
return v___x_2943_;
}
}
}
}
else
{
lean_object* v___x_2946_; lean_object* v___x_2947_; 
v___x_2946_ = lean_array_get_size(v_x_2917_);
lean_inc_ref(v_f_2926_);
v___x_2947_ = l_Lean_Meta_getFunInfoNArgs(v_f_2926_, v___x_2946_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_);
if (lean_obj_tag(v___x_2947_) == 0)
{
lean_object* v_a_2948_; lean_object* v_paramInfo_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; 
v_a_2948_ = lean_ctor_get(v___x_2947_, 0);
lean_inc(v_a_2948_);
lean_dec_ref(v___x_2947_);
v_paramInfo_2949_ = lean_ctor_get(v_a_2948_, 0);
lean_inc_ref(v_paramInfo_2949_);
lean_dec(v_a_2948_);
v___x_2950_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_2913_);
lean_inc_ref(v_pre_2912_);
v___x_2951_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg(v___x_2946_, v_paramInfo_2949_, v_pre_2912_, v_post_2913_, v_usedLetOnly_2914_, v_skipConstInApp_2915_, v_skipInstances_2911_, v___x_2950_, v_x_2917_, v___y_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_);
lean_dec_ref(v_paramInfo_2949_);
if (lean_obj_tag(v___x_2951_) == 0)
{
lean_object* v_a_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; 
v_a_2952_ = lean_ctor_get(v___x_2951_, 0);
lean_inc(v_a_2952_);
lean_dec_ref(v___x_2951_);
v___x_2953_ = l_Lean_mkAppN(v_f_2926_, v_a_2952_);
lean_dec(v_a_2952_);
v___x_2954_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_2912_, v_post_2913_, v_usedLetOnly_2914_, v_skipConstInApp_2915_, v_skipInstances_2911_, v___x_2953_, v___y_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_);
return v___x_2954_;
}
else
{
lean_object* v_a_2955_; lean_object* v___x_2957_; uint8_t v_isShared_2958_; uint8_t v_isSharedCheck_2962_; 
lean_dec_ref(v_f_2926_);
lean_dec_ref(v_post_2913_);
lean_dec_ref(v_pre_2912_);
v_a_2955_ = lean_ctor_get(v___x_2951_, 0);
v_isSharedCheck_2962_ = !lean_is_exclusive(v___x_2951_);
if (v_isSharedCheck_2962_ == 0)
{
v___x_2957_ = v___x_2951_;
v_isShared_2958_ = v_isSharedCheck_2962_;
goto v_resetjp_2956_;
}
else
{
lean_inc(v_a_2955_);
lean_dec(v___x_2951_);
v___x_2957_ = lean_box(0);
v_isShared_2958_ = v_isSharedCheck_2962_;
goto v_resetjp_2956_;
}
v_resetjp_2956_:
{
lean_object* v___x_2960_; 
if (v_isShared_2958_ == 0)
{
v___x_2960_ = v___x_2957_;
goto v_reusejp_2959_;
}
else
{
lean_object* v_reuseFailAlloc_2961_; 
v_reuseFailAlloc_2961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2961_, 0, v_a_2955_);
v___x_2960_ = v_reuseFailAlloc_2961_;
goto v_reusejp_2959_;
}
v_reusejp_2959_:
{
return v___x_2960_;
}
}
}
}
else
{
lean_object* v_a_2963_; lean_object* v___x_2965_; uint8_t v_isShared_2966_; uint8_t v_isSharedCheck_2970_; 
lean_dec_ref(v_f_2926_);
lean_dec_ref(v_x_2917_);
lean_dec_ref(v_post_2913_);
lean_dec_ref(v_pre_2912_);
v_a_2963_ = lean_ctor_get(v___x_2947_, 0);
v_isSharedCheck_2970_ = !lean_is_exclusive(v___x_2947_);
if (v_isSharedCheck_2970_ == 0)
{
v___x_2965_ = v___x_2947_;
v_isShared_2966_ = v_isSharedCheck_2970_;
goto v_resetjp_2964_;
}
else
{
lean_inc(v_a_2963_);
lean_dec(v___x_2947_);
v___x_2965_ = lean_box(0);
v_isShared_2966_ = v_isSharedCheck_2970_;
goto v_resetjp_2964_;
}
v_resetjp_2964_:
{
lean_object* v___x_2968_; 
if (v_isShared_2966_ == 0)
{
v___x_2968_ = v___x_2965_;
goto v_reusejp_2967_;
}
else
{
lean_object* v_reuseFailAlloc_2969_; 
v_reuseFailAlloc_2969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2969_, 0, v_a_2963_);
v___x_2968_ = v_reuseFailAlloc_2969_;
goto v_reusejp_2967_;
}
v_reusejp_2967_:
{
return v___x_2968_;
}
}
}
}
}
v___jp_2971_:
{
lean_object* v___x_2972_; 
lean_inc_ref(v_post_2913_);
lean_inc_ref(v_pre_2912_);
v___x_2972_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2912_, v_post_2913_, v_usedLetOnly_2914_, v_skipConstInApp_2915_, v_skipInstances_2911_, v_x_2916_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_);
if (lean_obj_tag(v___x_2972_) == 0)
{
lean_object* v_a_2973_; 
v_a_2973_ = lean_ctor_get(v___x_2972_, 0);
lean_inc(v_a_2973_);
lean_dec_ref(v___x_2972_);
v_f_2926_ = v_a_2973_;
v___y_2927_ = v___y_2919_;
v___y_2928_ = v___y_2920_;
v___y_2929_ = v___y_2921_;
v___y_2930_ = v___y_2922_;
v___y_2931_ = v___y_2923_;
goto v___jp_2925_;
}
else
{
lean_dec_ref(v_x_2917_);
lean_dec_ref(v_post_2913_);
lean_dec_ref(v_pre_2912_);
return v___x_2972_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__1(lean_object* v_pre_2981_, lean_object* v_e_2982_, lean_object* v_post_2983_, uint8_t v_usedLetOnly_2984_, uint8_t v_skipConstInApp_2985_, uint8_t v_skipInstances_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_){
_start:
{
lean_object* v___x_2993_; 
lean_inc_ref(v_pre_2981_);
lean_inc(v___y_2991_);
lean_inc_ref(v___y_2990_);
lean_inc(v___y_2989_);
lean_inc_ref(v___y_2988_);
lean_inc_ref(v_e_2982_);
v___x_2993_ = lean_apply_6(v_pre_2981_, v_e_2982_, v___y_2988_, v___y_2989_, v___y_2990_, v___y_2991_, lean_box(0));
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
lean_dec_ref(v_post_2983_);
lean_dec_ref(v_e_2982_);
lean_dec_ref(v_pre_2981_);
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
lean_dec_ref(v_e_2982_);
v_e_3038_ = lean_ctor_get(v_a_2994_, 0);
lean_inc_ref(v_e_3038_);
lean_dec_ref(v_a_2994_);
v___x_3039_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2981_, v_post_2983_, v_usedLetOnly_2984_, v_skipConstInApp_2985_, v_skipInstances_2986_, v_e_3038_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_, v___y_2991_);
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
v___y_2999_ = v_e_2982_;
goto v___jp_2998_;
}
else
{
lean_object* v_val_3041_; 
lean_dec_ref(v_e_2982_);
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
v___x_3001_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8(v_pre_2981_, v_post_2983_, v_usedLetOnly_2984_, v_skipConstInApp_2985_, v_skipInstances_2986_, v___x_3000_, v___y_2999_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_, v___y_2991_);
return v___x_3001_;
}
case 6:
{
lean_object* v___x_3002_; lean_object* v___x_3003_; 
v___x_3002_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__1___closed__0));
v___x_3003_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9(v_pre_2981_, v_post_2983_, v_usedLetOnly_2984_, v_skipConstInApp_2985_, v_skipInstances_2986_, v___x_3002_, v___y_2999_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_, v___y_2991_);
return v___x_3003_;
}
case 8:
{
lean_object* v___x_3004_; lean_object* v___x_3005_; 
v___x_3004_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__1___closed__0));
v___x_3005_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10(v_pre_2981_, v_post_2983_, v_usedLetOnly_2984_, v_skipConstInApp_2985_, v_skipInstances_2986_, v___x_3004_, v___y_2999_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_, v___y_2991_);
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
v___x_3011_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__11(v_skipInstances_2986_, v_pre_2981_, v_post_2983_, v_usedLetOnly_2984_, v_skipConstInApp_2985_, v___y_2999_, v___x_3008_, v___x_3010_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_, v___y_2991_);
return v___x_3011_;
}
case 10:
{
lean_object* v_data_3012_; lean_object* v_expr_3013_; lean_object* v___x_3014_; 
v_data_3012_ = lean_ctor_get(v___y_2999_, 0);
v_expr_3013_ = lean_ctor_get(v___y_2999_, 1);
lean_inc_ref(v_expr_3013_);
lean_inc_ref(v_post_2983_);
lean_inc_ref(v_pre_2981_);
v___x_3014_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2981_, v_post_2983_, v_usedLetOnly_2984_, v_skipConstInApp_2985_, v_skipInstances_2986_, v_expr_3013_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_, v___y_2991_);
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
v___x_3020_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_2981_, v_post_2983_, v_usedLetOnly_2984_, v_skipConstInApp_2985_, v_skipInstances_2986_, v___x_3019_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_, v___y_2991_);
return v___x_3020_;
}
else
{
lean_object* v___x_3021_; 
lean_dec(v_a_3015_);
v___x_3021_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_2981_, v_post_2983_, v_usedLetOnly_2984_, v_skipConstInApp_2985_, v_skipInstances_2986_, v___y_2999_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_, v___y_2991_);
return v___x_3021_;
}
}
else
{
lean_dec_ref(v___y_2999_);
lean_dec_ref(v_post_2983_);
lean_dec_ref(v_pre_2981_);
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
lean_inc_ref(v_post_2983_);
lean_inc_ref(v_pre_2981_);
v___x_3025_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2981_, v_post_2983_, v_usedLetOnly_2984_, v_skipConstInApp_2985_, v_skipInstances_2986_, v_struct_3024_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_, v___y_2991_);
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
v___x_3031_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_2981_, v_post_2983_, v_usedLetOnly_2984_, v_skipConstInApp_2985_, v_skipInstances_2986_, v___x_3030_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_, v___y_2991_);
return v___x_3031_;
}
else
{
lean_object* v___x_3032_; 
lean_dec(v_a_3026_);
v___x_3032_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_2981_, v_post_2983_, v_usedLetOnly_2984_, v_skipConstInApp_2985_, v_skipInstances_2986_, v___y_2999_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_, v___y_2991_);
return v___x_3032_;
}
}
else
{
lean_dec_ref(v___y_2999_);
lean_dec_ref(v_post_2983_);
lean_dec_ref(v_pre_2981_);
return v___x_3025_;
}
}
default: 
{
lean_object* v___x_3033_; 
v___x_3033_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_2981_, v_post_2983_, v_usedLetOnly_2984_, v_skipConstInApp_2985_, v_skipInstances_2986_, v___y_2999_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_, v___y_2991_);
return v___x_3033_;
}
}
}
}
}
else
{
lean_object* v_a_3043_; lean_object* v___x_3045_; uint8_t v_isShared_3046_; uint8_t v_isSharedCheck_3050_; 
lean_dec_ref(v_post_2983_);
lean_dec_ref(v_e_2982_);
lean_dec_ref(v_pre_2981_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__1___boxed(lean_object* v_pre_3051_, lean_object* v_e_3052_, lean_object* v_post_3053_, lean_object* v_usedLetOnly_3054_, lean_object* v_skipConstInApp_3055_, lean_object* v_skipInstances_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_){
_start:
{
uint8_t v_usedLetOnly_boxed_3063_; uint8_t v_skipConstInApp_boxed_3064_; uint8_t v_skipInstances_boxed_3065_; lean_object* v_res_3066_; 
v_usedLetOnly_boxed_3063_ = lean_unbox(v_usedLetOnly_3054_);
v_skipConstInApp_boxed_3064_ = lean_unbox(v_skipConstInApp_3055_);
v_skipInstances_boxed_3065_ = lean_unbox(v_skipInstances_3056_);
v_res_3066_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__1(v_pre_3051_, v_e_3052_, v_post_3053_, v_usedLetOnly_boxed_3063_, v_skipConstInApp_boxed_3064_, v_skipInstances_boxed_3065_, v___y_3057_, v___y_3058_, v___y_3059_, v___y_3060_, v___y_3061_);
lean_dec(v___y_3061_);
lean_dec_ref(v___y_3060_);
lean_dec(v___y_3059_);
lean_dec_ref(v___y_3058_);
lean_dec(v___y_3057_);
return v_res_3066_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(lean_object* v_pre_3067_, lean_object* v_post_3068_, uint8_t v_usedLetOnly_3069_, uint8_t v_skipConstInApp_3070_, uint8_t v_skipInstances_3071_, lean_object* v_e_3072_, lean_object* v_a_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_){
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
lean_object* v_a_3081_; lean_object* v___x_3083_; uint8_t v_isShared_3084_; uint8_t v_isSharedCheck_3114_; 
v_a_3081_ = lean_ctor_get(v___x_3080_, 0);
v_isSharedCheck_3114_ = !lean_is_exclusive(v___x_3080_);
if (v_isSharedCheck_3114_ == 0)
{
v___x_3083_ = v___x_3080_;
v_isShared_3084_ = v_isSharedCheck_3114_;
goto v_resetjp_3082_;
}
else
{
lean_inc(v_a_3081_);
lean_dec(v___x_3080_);
v___x_3083_ = lean_box(0);
v_isShared_3084_ = v_isSharedCheck_3114_;
goto v_resetjp_3082_;
}
v_resetjp_3082_:
{
lean_object* v___x_3085_; 
v___x_3085_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___redArg(v_a_3081_, v_e_3072_);
lean_dec(v_a_3081_);
if (lean_obj_tag(v___x_3085_) == 0)
{
lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___f_3089_; lean_object* v___x_3090_; 
lean_del_object(v___x_3083_);
v___x_3086_ = lean_box(v_usedLetOnly_3069_);
v___x_3087_ = lean_box(v_skipConstInApp_3070_);
v___x_3088_ = lean_box(v_skipInstances_3071_);
lean_inc_ref(v_e_3072_);
v___f_3089_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__1___boxed), 12, 6);
lean_closure_set(v___f_3089_, 0, v_pre_3067_);
lean_closure_set(v___f_3089_, 1, v_e_3072_);
lean_closure_set(v___f_3089_, 2, v_post_3068_);
lean_closure_set(v___f_3089_, 3, v___x_3086_);
lean_closure_set(v___f_3089_, 4, v___x_3087_);
lean_closure_set(v___f_3089_, 5, v___x_3088_);
lean_inc_ref(v___y_3076_);
v___x_3090_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12___redArg(v___f_3089_, v_a_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_);
if (lean_obj_tag(v___x_3090_) == 0)
{
lean_object* v_a_3091_; lean_object* v___f_3092_; lean_object* v___x_3093_; 
v_a_3091_ = lean_ctor_get(v___x_3090_, 0);
lean_inc(v_a_3091_);
lean_dec_ref(v___x_3090_);
lean_inc(v_a_3091_);
lean_inc(v_a_3073_);
v___f_3092_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__2___boxed), 4, 3);
lean_closure_set(v___f_3092_, 0, v_a_3073_);
lean_closure_set(v___f_3092_, 1, v_e_3072_);
lean_closure_set(v___f_3092_, 2, v_a_3091_);
v___x_3093_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__0(lean_box(0), v___f_3092_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_);
if (lean_obj_tag(v___x_3093_) == 0)
{
lean_object* v___x_3095_; uint8_t v_isShared_3096_; uint8_t v_isSharedCheck_3100_; 
v_isSharedCheck_3100_ = !lean_is_exclusive(v___x_3093_);
if (v_isSharedCheck_3100_ == 0)
{
lean_object* v_unused_3101_; 
v_unused_3101_ = lean_ctor_get(v___x_3093_, 0);
lean_dec(v_unused_3101_);
v___x_3095_ = v___x_3093_;
v_isShared_3096_ = v_isSharedCheck_3100_;
goto v_resetjp_3094_;
}
else
{
lean_dec(v___x_3093_);
v___x_3095_ = lean_box(0);
v_isShared_3096_ = v_isSharedCheck_3100_;
goto v_resetjp_3094_;
}
v_resetjp_3094_:
{
lean_object* v___x_3098_; 
if (v_isShared_3096_ == 0)
{
lean_ctor_set(v___x_3095_, 0, v_a_3091_);
v___x_3098_ = v___x_3095_;
goto v_reusejp_3097_;
}
else
{
lean_object* v_reuseFailAlloc_3099_; 
v_reuseFailAlloc_3099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3099_, 0, v_a_3091_);
v___x_3098_ = v_reuseFailAlloc_3099_;
goto v_reusejp_3097_;
}
v_reusejp_3097_:
{
return v___x_3098_;
}
}
}
else
{
lean_object* v_a_3102_; lean_object* v___x_3104_; uint8_t v_isShared_3105_; uint8_t v_isSharedCheck_3109_; 
lean_dec(v_a_3091_);
v_a_3102_ = lean_ctor_get(v___x_3093_, 0);
v_isSharedCheck_3109_ = !lean_is_exclusive(v___x_3093_);
if (v_isSharedCheck_3109_ == 0)
{
v___x_3104_ = v___x_3093_;
v_isShared_3105_ = v_isSharedCheck_3109_;
goto v_resetjp_3103_;
}
else
{
lean_inc(v_a_3102_);
lean_dec(v___x_3093_);
v___x_3104_ = lean_box(0);
v_isShared_3105_ = v_isSharedCheck_3109_;
goto v_resetjp_3103_;
}
v_resetjp_3103_:
{
lean_object* v___x_3107_; 
if (v_isShared_3105_ == 0)
{
v___x_3107_ = v___x_3104_;
goto v_reusejp_3106_;
}
else
{
lean_object* v_reuseFailAlloc_3108_; 
v_reuseFailAlloc_3108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3108_, 0, v_a_3102_);
v___x_3107_ = v_reuseFailAlloc_3108_;
goto v_reusejp_3106_;
}
v_reusejp_3106_:
{
return v___x_3107_;
}
}
}
}
else
{
lean_dec_ref(v_e_3072_);
return v___x_3090_;
}
}
else
{
lean_object* v_val_3110_; lean_object* v___x_3112_; 
lean_dec_ref(v_e_3072_);
lean_dec_ref(v_post_3068_);
lean_dec_ref(v_pre_3067_);
v_val_3110_ = lean_ctor_get(v___x_3085_, 0);
lean_inc(v_val_3110_);
lean_dec_ref(v___x_3085_);
if (v_isShared_3084_ == 0)
{
lean_ctor_set(v___x_3083_, 0, v_val_3110_);
v___x_3112_ = v___x_3083_;
goto v_reusejp_3111_;
}
else
{
lean_object* v_reuseFailAlloc_3113_; 
v_reuseFailAlloc_3113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3113_, 0, v_val_3110_);
v___x_3112_ = v_reuseFailAlloc_3113_;
goto v_reusejp_3111_;
}
v_reusejp_3111_:
{
return v___x_3112_;
}
}
}
}
else
{
lean_object* v_a_3115_; lean_object* v___x_3117_; uint8_t v_isShared_3118_; uint8_t v_isSharedCheck_3122_; 
lean_dec_ref(v_e_3072_);
lean_dec_ref(v_post_3068_);
lean_dec_ref(v_pre_3067_);
v_a_3115_ = lean_ctor_get(v___x_3080_, 0);
v_isSharedCheck_3122_ = !lean_is_exclusive(v___x_3080_);
if (v_isSharedCheck_3122_ == 0)
{
v___x_3117_ = v___x_3080_;
v_isShared_3118_ = v_isSharedCheck_3122_;
goto v_resetjp_3116_;
}
else
{
lean_inc(v_a_3115_);
lean_dec(v___x_3080_);
v___x_3117_ = lean_box(0);
v_isShared_3118_ = v_isSharedCheck_3122_;
goto v_resetjp_3116_;
}
v_resetjp_3116_:
{
lean_object* v___x_3120_; 
if (v_isShared_3118_ == 0)
{
v___x_3120_ = v___x_3117_;
goto v_reusejp_3119_;
}
else
{
lean_object* v_reuseFailAlloc_3121_; 
v_reuseFailAlloc_3121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3121_, 0, v_a_3115_);
v___x_3120_ = v_reuseFailAlloc_3121_;
goto v_reusejp_3119_;
}
v_reusejp_3119_:
{
return v___x_3120_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8___lam__0___boxed(lean_object* v_fvars_3123_, lean_object* v_pre_3124_, lean_object* v_post_3125_, lean_object* v_usedLetOnly_3126_, lean_object* v_skipConstInApp_3127_, lean_object* v_skipInstances_3128_, lean_object* v_body_3129_, lean_object* v_x_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_){
_start:
{
uint8_t v_usedLetOnly_boxed_3137_; uint8_t v_skipConstInApp_boxed_3138_; uint8_t v_skipInstances_boxed_3139_; lean_object* v_res_3140_; 
v_usedLetOnly_boxed_3137_ = lean_unbox(v_usedLetOnly_3126_);
v_skipConstInApp_boxed_3138_ = lean_unbox(v_skipConstInApp_3127_);
v_skipInstances_boxed_3139_ = lean_unbox(v_skipInstances_3128_);
v_res_3140_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8___lam__0(v_fvars_3123_, v_pre_3124_, v_post_3125_, v_usedLetOnly_boxed_3137_, v_skipConstInApp_boxed_3138_, v_skipInstances_boxed_3139_, v_body_3129_, v_x_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_);
lean_dec(v___y_3135_);
lean_dec_ref(v___y_3134_);
lean_dec(v___y_3133_);
lean_dec_ref(v___y_3132_);
lean_dec(v___y_3131_);
return v_res_3140_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8(lean_object* v_pre_3141_, lean_object* v_post_3142_, uint8_t v_usedLetOnly_3143_, uint8_t v_skipConstInApp_3144_, uint8_t v_skipInstances_3145_, lean_object* v_fvars_3146_, lean_object* v_e_3147_, lean_object* v_a_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_){
_start:
{
if (lean_obj_tag(v_e_3147_) == 7)
{
lean_object* v_binderName_3154_; lean_object* v_binderType_3155_; lean_object* v_body_3156_; uint8_t v_binderInfo_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; 
v_binderName_3154_ = lean_ctor_get(v_e_3147_, 0);
lean_inc(v_binderName_3154_);
v_binderType_3155_ = lean_ctor_get(v_e_3147_, 1);
lean_inc_ref(v_binderType_3155_);
v_body_3156_ = lean_ctor_get(v_e_3147_, 2);
lean_inc_ref(v_body_3156_);
v_binderInfo_3157_ = lean_ctor_get_uint8(v_e_3147_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_3147_);
v___x_3158_ = lean_expr_instantiate_rev(v_binderType_3155_, v_fvars_3146_);
lean_dec_ref(v_binderType_3155_);
lean_inc_ref(v_post_3142_);
lean_inc_ref(v_pre_3141_);
v___x_3159_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_3141_, v_post_3142_, v_usedLetOnly_3143_, v_skipConstInApp_3144_, v_skipInstances_3145_, v___x_3158_, v_a_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_);
if (lean_obj_tag(v___x_3159_) == 0)
{
lean_object* v_a_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___f_3164_; uint8_t v___x_3165_; lean_object* v___x_3166_; 
v_a_3160_ = lean_ctor_get(v___x_3159_, 0);
lean_inc(v_a_3160_);
lean_dec_ref(v___x_3159_);
v___x_3161_ = lean_box(v_usedLetOnly_3143_);
v___x_3162_ = lean_box(v_skipConstInApp_3144_);
v___x_3163_ = lean_box(v_skipInstances_3145_);
v___f_3164_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8___lam__0___boxed), 14, 7);
lean_closure_set(v___f_3164_, 0, v_fvars_3146_);
lean_closure_set(v___f_3164_, 1, v_pre_3141_);
lean_closure_set(v___f_3164_, 2, v_post_3142_);
lean_closure_set(v___f_3164_, 3, v___x_3161_);
lean_closure_set(v___f_3164_, 4, v___x_3162_);
lean_closure_set(v___f_3164_, 5, v___x_3163_);
lean_closure_set(v___f_3164_, 6, v_body_3156_);
v___x_3165_ = 0;
v___x_3166_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg(v_binderName_3154_, v_binderInfo_3157_, v_a_3160_, v___f_3164_, v___x_3165_, v_a_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_);
return v___x_3166_;
}
else
{
lean_dec_ref(v_body_3156_);
lean_dec(v_binderName_3154_);
lean_dec_ref(v_fvars_3146_);
lean_dec_ref(v_post_3142_);
lean_dec_ref(v_pre_3141_);
return v___x_3159_;
}
}
else
{
lean_object* v___x_3167_; lean_object* v___x_3168_; 
v___x_3167_ = lean_expr_instantiate_rev(v_e_3147_, v_fvars_3146_);
lean_dec_ref(v_e_3147_);
lean_inc_ref(v_post_3142_);
lean_inc_ref(v_pre_3141_);
v___x_3168_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_3141_, v_post_3142_, v_usedLetOnly_3143_, v_skipConstInApp_3144_, v_skipInstances_3145_, v___x_3167_, v_a_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_);
if (lean_obj_tag(v___x_3168_) == 0)
{
lean_object* v_a_3169_; uint8_t v___x_3170_; uint8_t v___x_3171_; uint8_t v___x_3172_; lean_object* v___x_3173_; 
v_a_3169_ = lean_ctor_get(v___x_3168_, 0);
lean_inc(v_a_3169_);
lean_dec_ref(v___x_3168_);
v___x_3170_ = 0;
v___x_3171_ = 1;
v___x_3172_ = 1;
v___x_3173_ = l_Lean_Meta_mkForallFVars(v_fvars_3146_, v_a_3169_, v___x_3170_, v_usedLetOnly_3143_, v___x_3171_, v___x_3172_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_);
lean_dec_ref(v_fvars_3146_);
if (lean_obj_tag(v___x_3173_) == 0)
{
lean_object* v_a_3174_; lean_object* v___x_3175_; 
v_a_3174_ = lean_ctor_get(v___x_3173_, 0);
lean_inc(v_a_3174_);
lean_dec_ref(v___x_3173_);
v___x_3175_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_3141_, v_post_3142_, v_usedLetOnly_3143_, v_skipConstInApp_3144_, v_skipInstances_3145_, v_a_3174_, v_a_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_);
return v___x_3175_;
}
else
{
lean_dec_ref(v_post_3142_);
lean_dec_ref(v_pre_3141_);
return v___x_3173_;
}
}
else
{
lean_dec_ref(v_fvars_3146_);
lean_dec_ref(v_post_3142_);
lean_dec_ref(v_pre_3141_);
return v___x_3168_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8___lam__0(lean_object* v_fvars_3176_, lean_object* v_pre_3177_, lean_object* v_post_3178_, uint8_t v_usedLetOnly_3179_, uint8_t v_skipConstInApp_3180_, uint8_t v_skipInstances_3181_, lean_object* v_body_3182_, lean_object* v_x_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_){
_start:
{
lean_object* v___x_3190_; lean_object* v___x_3191_; 
v___x_3190_ = lean_array_push(v_fvars_3176_, v_x_3183_);
v___x_3191_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8(v_pre_3177_, v_post_3178_, v_usedLetOnly_3179_, v_skipConstInApp_3180_, v_skipInstances_3181_, v___x_3190_, v_body_3182_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_);
return v___x_3191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5___boxed(lean_object* v_pre_3192_, lean_object* v_post_3193_, lean_object* v_usedLetOnly_3194_, lean_object* v_skipConstInApp_3195_, lean_object* v_skipInstances_3196_, lean_object* v_e_3197_, lean_object* v_a_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_){
_start:
{
uint8_t v_usedLetOnly_boxed_3204_; uint8_t v_skipConstInApp_boxed_3205_; uint8_t v_skipInstances_boxed_3206_; lean_object* v_res_3207_; 
v_usedLetOnly_boxed_3204_ = lean_unbox(v_usedLetOnly_3194_);
v_skipConstInApp_boxed_3205_ = lean_unbox(v_skipConstInApp_3195_);
v_skipInstances_boxed_3206_ = lean_unbox(v_skipInstances_3196_);
v_res_3207_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_3192_, v_post_3193_, v_usedLetOnly_boxed_3204_, v_skipConstInApp_boxed_3205_, v_skipInstances_boxed_3206_, v_e_3197_, v_a_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_);
lean_dec(v___y_3202_);
lean_dec_ref(v___y_3201_);
lean_dec(v___y_3200_);
lean_dec_ref(v___y_3199_);
lean_dec(v_a_3198_);
return v_res_3207_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__4___boxed(lean_object* v_pre_3208_, lean_object* v_post_3209_, lean_object* v_usedLetOnly_3210_, lean_object* v_skipConstInApp_3211_, lean_object* v_skipInstances_3212_, lean_object* v_sz_3213_, lean_object* v_i_3214_, lean_object* v_bs_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_){
_start:
{
uint8_t v_usedLetOnly_boxed_3222_; uint8_t v_skipConstInApp_boxed_3223_; uint8_t v_skipInstances_boxed_3224_; size_t v_sz_boxed_3225_; size_t v_i_boxed_3226_; lean_object* v_res_3227_; 
v_usedLetOnly_boxed_3222_ = lean_unbox(v_usedLetOnly_3210_);
v_skipConstInApp_boxed_3223_ = lean_unbox(v_skipConstInApp_3211_);
v_skipInstances_boxed_3224_ = lean_unbox(v_skipInstances_3212_);
v_sz_boxed_3225_ = lean_unbox_usize(v_sz_3213_);
lean_dec(v_sz_3213_);
v_i_boxed_3226_ = lean_unbox_usize(v_i_3214_);
lean_dec(v_i_3214_);
v_res_3227_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__4(v_pre_3208_, v_post_3209_, v_usedLetOnly_boxed_3222_, v_skipConstInApp_boxed_3223_, v_skipInstances_boxed_3224_, v_sz_boxed_3225_, v_i_boxed_3226_, v_bs_3215_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_);
lean_dec(v___y_3220_);
lean_dec_ref(v___y_3219_);
lean_dec(v___y_3218_);
lean_dec_ref(v___y_3217_);
lean_dec(v___y_3216_);
return v_res_3227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___boxed(lean_object* v_pre_3228_, lean_object* v_post_3229_, lean_object* v_usedLetOnly_3230_, lean_object* v_skipConstInApp_3231_, lean_object* v_skipInstances_3232_, lean_object* v_e_3233_, lean_object* v_a_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_){
_start:
{
uint8_t v_usedLetOnly_boxed_3240_; uint8_t v_skipConstInApp_boxed_3241_; uint8_t v_skipInstances_boxed_3242_; lean_object* v_res_3243_; 
v_usedLetOnly_boxed_3240_ = lean_unbox(v_usedLetOnly_3230_);
v_skipConstInApp_boxed_3241_ = lean_unbox(v_skipConstInApp_3231_);
v_skipInstances_boxed_3242_ = lean_unbox(v_skipInstances_3232_);
v_res_3243_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_3228_, v_post_3229_, v_usedLetOnly_boxed_3240_, v_skipConstInApp_boxed_3241_, v_skipInstances_boxed_3242_, v_e_3233_, v_a_3234_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_);
lean_dec(v___y_3238_);
lean_dec_ref(v___y_3237_);
lean_dec(v___y_3236_);
lean_dec_ref(v___y_3235_);
lean_dec(v_a_3234_);
return v_res_3243_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8___boxed(lean_object* v_pre_3244_, lean_object* v_post_3245_, lean_object* v_usedLetOnly_3246_, lean_object* v_skipConstInApp_3247_, lean_object* v_skipInstances_3248_, lean_object* v_fvars_3249_, lean_object* v_e_3250_, lean_object* v_a_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_){
_start:
{
uint8_t v_usedLetOnly_boxed_3257_; uint8_t v_skipConstInApp_boxed_3258_; uint8_t v_skipInstances_boxed_3259_; lean_object* v_res_3260_; 
v_usedLetOnly_boxed_3257_ = lean_unbox(v_usedLetOnly_3246_);
v_skipConstInApp_boxed_3258_ = lean_unbox(v_skipConstInApp_3247_);
v_skipInstances_boxed_3259_ = lean_unbox(v_skipInstances_3248_);
v_res_3260_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8(v_pre_3244_, v_post_3245_, v_usedLetOnly_boxed_3257_, v_skipConstInApp_boxed_3258_, v_skipInstances_boxed_3259_, v_fvars_3249_, v_e_3250_, v_a_3251_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_);
lean_dec(v___y_3255_);
lean_dec_ref(v___y_3254_);
lean_dec(v___y_3253_);
lean_dec_ref(v___y_3252_);
lean_dec(v_a_3251_);
return v_res_3260_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9___boxed(lean_object* v_pre_3261_, lean_object* v_post_3262_, lean_object* v_usedLetOnly_3263_, lean_object* v_skipConstInApp_3264_, lean_object* v_skipInstances_3265_, lean_object* v_fvars_3266_, lean_object* v_e_3267_, lean_object* v_a_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_){
_start:
{
uint8_t v_usedLetOnly_boxed_3274_; uint8_t v_skipConstInApp_boxed_3275_; uint8_t v_skipInstances_boxed_3276_; lean_object* v_res_3277_; 
v_usedLetOnly_boxed_3274_ = lean_unbox(v_usedLetOnly_3263_);
v_skipConstInApp_boxed_3275_ = lean_unbox(v_skipConstInApp_3264_);
v_skipInstances_boxed_3276_ = lean_unbox(v_skipInstances_3265_);
v_res_3277_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9(v_pre_3261_, v_post_3262_, v_usedLetOnly_boxed_3274_, v_skipConstInApp_boxed_3275_, v_skipInstances_boxed_3276_, v_fvars_3266_, v_e_3267_, v_a_3268_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_);
lean_dec(v___y_3272_);
lean_dec_ref(v___y_3271_);
lean_dec(v___y_3270_);
lean_dec_ref(v___y_3269_);
lean_dec(v_a_3268_);
return v_res_3277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10___boxed(lean_object* v_pre_3278_, lean_object* v_post_3279_, lean_object* v_usedLetOnly_3280_, lean_object* v_skipConstInApp_3281_, lean_object* v_skipInstances_3282_, lean_object* v_fvars_3283_, lean_object* v_e_3284_, lean_object* v_a_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_){
_start:
{
uint8_t v_usedLetOnly_boxed_3291_; uint8_t v_skipConstInApp_boxed_3292_; uint8_t v_skipInstances_boxed_3293_; lean_object* v_res_3294_; 
v_usedLetOnly_boxed_3291_ = lean_unbox(v_usedLetOnly_3280_);
v_skipConstInApp_boxed_3292_ = lean_unbox(v_skipConstInApp_3281_);
v_skipInstances_boxed_3293_ = lean_unbox(v_skipInstances_3282_);
v_res_3294_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10(v_pre_3278_, v_post_3279_, v_usedLetOnly_boxed_3291_, v_skipConstInApp_boxed_3292_, v_skipInstances_boxed_3293_, v_fvars_3283_, v_e_3284_, v_a_3285_, v___y_3286_, v___y_3287_, v___y_3288_, v___y_3289_);
lean_dec(v___y_3289_);
lean_dec_ref(v___y_3288_);
lean_dec(v___y_3287_);
lean_dec_ref(v___y_3286_);
lean_dec(v_a_3285_);
return v_res_3294_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___boxed(lean_object* v_upperBound_3295_, lean_object* v___x_3296_, lean_object* v_pre_3297_, lean_object* v_post_3298_, lean_object* v_usedLetOnly_3299_, lean_object* v_skipConstInApp_3300_, lean_object* v_skipInstances_3301_, lean_object* v_a_3302_, lean_object* v_b_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_){
_start:
{
uint8_t v_usedLetOnly_boxed_3310_; uint8_t v_skipConstInApp_boxed_3311_; uint8_t v_skipInstances_boxed_3312_; lean_object* v_res_3313_; 
v_usedLetOnly_boxed_3310_ = lean_unbox(v_usedLetOnly_3299_);
v_skipConstInApp_boxed_3311_ = lean_unbox(v_skipConstInApp_3300_);
v_skipInstances_boxed_3312_ = lean_unbox(v_skipInstances_3301_);
v_res_3313_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg(v_upperBound_3295_, v___x_3296_, v_pre_3297_, v_post_3298_, v_usedLetOnly_boxed_3310_, v_skipConstInApp_boxed_3311_, v_skipInstances_boxed_3312_, v_a_3302_, v_b_3303_, v___y_3304_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_);
lean_dec(v___y_3308_);
lean_dec_ref(v___y_3307_);
lean_dec(v___y_3306_);
lean_dec_ref(v___y_3305_);
lean_dec(v___y_3304_);
lean_dec_ref(v___x_3296_);
lean_dec(v_upperBound_3295_);
return v_res_3313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__11___boxed(lean_object* v_skipInstances_3314_, lean_object* v_pre_3315_, lean_object* v_post_3316_, lean_object* v_usedLetOnly_3317_, lean_object* v_skipConstInApp_3318_, lean_object* v_x_3319_, lean_object* v_x_3320_, lean_object* v_x_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_){
_start:
{
uint8_t v_skipInstances_boxed_3328_; uint8_t v_usedLetOnly_boxed_3329_; uint8_t v_skipConstInApp_boxed_3330_; lean_object* v_res_3331_; 
v_skipInstances_boxed_3328_ = lean_unbox(v_skipInstances_3314_);
v_usedLetOnly_boxed_3329_ = lean_unbox(v_usedLetOnly_3317_);
v_skipConstInApp_boxed_3330_ = lean_unbox(v_skipConstInApp_3318_);
v_res_3331_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__11(v_skipInstances_boxed_3328_, v_pre_3315_, v_post_3316_, v_usedLetOnly_boxed_3329_, v_skipConstInApp_boxed_3330_, v_x_3319_, v_x_3320_, v_x_3321_, v___y_3322_, v___y_3323_, v___y_3324_, v___y_3325_, v___y_3326_);
lean_dec(v___y_3326_);
lean_dec_ref(v___y_3325_);
lean_dec(v___y_3324_);
lean_dec_ref(v___y_3323_);
lean_dec(v___y_3322_);
return v_res_3331_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__0(void){
_start:
{
lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; 
v___x_3332_ = lean_box(0);
v___x_3333_ = lean_unsigned_to_nat(16u);
v___x_3334_ = lean_mk_array(v___x_3333_, v___x_3332_);
return v___x_3334_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__1(void){
_start:
{
lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; 
v___x_3335_ = lean_obj_once(&l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__0, &l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__0_once, _init_l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__0);
v___x_3336_ = lean_unsigned_to_nat(0u);
v___x_3337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3337_, 0, v___x_3336_);
lean_ctor_set(v___x_3337_, 1, v___x_3335_);
return v___x_3337_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__2(void){
_start:
{
lean_object* v___x_3338_; lean_object* v___x_3339_; 
v___x_3338_ = lean_obj_once(&l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__1, &l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__1_once, _init_l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__1);
v___x_3339_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_3339_, 0, lean_box(0));
lean_closure_set(v___x_3339_, 1, lean_box(0));
lean_closure_set(v___x_3339_, 2, v___x_3338_);
return v___x_3339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3(lean_object* v_input_3340_, lean_object* v_pre_3341_, lean_object* v_post_3342_, uint8_t v_usedLetOnly_3343_, uint8_t v_skipConstInApp_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_){
_start:
{
lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v_a_3352_; uint8_t v___x_3353_; lean_object* v___x_3354_; 
v___x_3350_ = lean_obj_once(&l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__2, &l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__2_once, _init_l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__2);
v___x_3351_ = l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___lam__0(lean_box(0), v___x_3350_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_);
v_a_3352_ = lean_ctor_get(v___x_3351_, 0);
lean_inc(v_a_3352_);
lean_dec_ref(v___x_3351_);
v___x_3353_ = 0;
v___x_3354_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_3341_, v_post_3342_, v_usedLetOnly_3343_, v_skipConstInApp_3344_, v___x_3353_, v_input_3340_, v_a_3352_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_);
if (lean_obj_tag(v___x_3354_) == 0)
{
lean_object* v_a_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3359_; uint8_t v_isShared_3360_; uint8_t v_isSharedCheck_3364_; 
v_a_3355_ = lean_ctor_get(v___x_3354_, 0);
lean_inc(v_a_3355_);
lean_dec_ref(v___x_3354_);
v___x_3356_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3356_, 0, lean_box(0));
lean_closure_set(v___x_3356_, 1, lean_box(0));
lean_closure_set(v___x_3356_, 2, v_a_3352_);
v___x_3357_ = l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___lam__0(lean_box(0), v___x_3356_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_);
v_isSharedCheck_3364_ = !lean_is_exclusive(v___x_3357_);
if (v_isSharedCheck_3364_ == 0)
{
lean_object* v_unused_3365_; 
v_unused_3365_ = lean_ctor_get(v___x_3357_, 0);
lean_dec(v_unused_3365_);
v___x_3359_ = v___x_3357_;
v_isShared_3360_ = v_isSharedCheck_3364_;
goto v_resetjp_3358_;
}
else
{
lean_dec(v___x_3357_);
v___x_3359_ = lean_box(0);
v_isShared_3360_ = v_isSharedCheck_3364_;
goto v_resetjp_3358_;
}
v_resetjp_3358_:
{
lean_object* v___x_3362_; 
if (v_isShared_3360_ == 0)
{
lean_ctor_set(v___x_3359_, 0, v_a_3355_);
v___x_3362_ = v___x_3359_;
goto v_reusejp_3361_;
}
else
{
lean_object* v_reuseFailAlloc_3363_; 
v_reuseFailAlloc_3363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3363_, 0, v_a_3355_);
v___x_3362_ = v_reuseFailAlloc_3363_;
goto v_reusejp_3361_;
}
v_reusejp_3361_:
{
return v___x_3362_;
}
}
}
else
{
lean_dec(v_a_3352_);
return v___x_3354_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___boxed(lean_object* v_input_3366_, lean_object* v_pre_3367_, lean_object* v_post_3368_, lean_object* v_usedLetOnly_3369_, lean_object* v_skipConstInApp_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_){
_start:
{
uint8_t v_usedLetOnly_boxed_3376_; uint8_t v_skipConstInApp_boxed_3377_; lean_object* v_res_3378_; 
v_usedLetOnly_boxed_3376_ = lean_unbox(v_usedLetOnly_3369_);
v_skipConstInApp_boxed_3377_ = lean_unbox(v_skipConstInApp_3370_);
v_res_3378_ = l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3(v_input_3366_, v_pre_3367_, v_post_3368_, v_usedLetOnly_boxed_3376_, v_skipConstInApp_boxed_3377_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_);
lean_dec(v___y_3374_);
lean_dec_ref(v___y_3373_);
lean_dec(v___y_3372_);
lean_dec_ref(v___y_3371_);
return v_res_3378_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet(lean_object* v_e_3381_, lean_object* v_a_3382_, lean_object* v_a_3383_, lean_object* v_a_3384_, lean_object* v_a_3385_){
_start:
{
lean_object* v___f_3387_; lean_object* v___f_3388_; uint8_t v___x_3389_; lean_object* v___x_3390_; 
v___f_3387_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___closed__0));
v___f_3388_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___closed__1));
v___x_3389_ = 0;
v___x_3390_ = l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3(v_e_3381_, v___f_3388_, v___f_3387_, v___x_3389_, v___x_3389_, v_a_3382_, v_a_3383_, v_a_3384_, v_a_3385_);
return v___x_3390_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___boxed(lean_object* v_e_3391_, lean_object* v_a_3392_, lean_object* v_a_3393_, lean_object* v_a_3394_, lean_object* v_a_3395_, lean_object* v_a_3396_){
_start:
{
lean_object* v_res_3397_; 
v_res_3397_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet(v_e_3391_, v_a_3392_, v_a_3393_, v_a_3394_, v_a_3395_);
lean_dec(v_a_3395_);
lean_dec_ref(v_a_3394_);
lean_dec(v_a_3393_);
lean_dec_ref(v_a_3392_);
return v_res_3397_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6(lean_object* v_upperBound_3398_, lean_object* v___x_3399_, lean_object* v_pre_3400_, lean_object* v_post_3401_, uint8_t v_usedLetOnly_3402_, uint8_t v_skipConstInApp_3403_, uint8_t v_skipInstances_3404_, lean_object* v___x_3405_, lean_object* v_inst_3406_, lean_object* v_R_3407_, lean_object* v_a_3408_, lean_object* v_b_3409_, lean_object* v_c_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_){
_start:
{
lean_object* v___x_3417_; 
v___x_3417_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg(v_upperBound_3398_, v___x_3399_, v_pre_3400_, v_post_3401_, v_usedLetOnly_3402_, v_skipConstInApp_3403_, v_skipInstances_3404_, v_a_3408_, v_b_3409_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_);
return v___x_3417_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___boxed(lean_object** _args){
lean_object* v_upperBound_3418_ = _args[0];
lean_object* v___x_3419_ = _args[1];
lean_object* v_pre_3420_ = _args[2];
lean_object* v_post_3421_ = _args[3];
lean_object* v_usedLetOnly_3422_ = _args[4];
lean_object* v_skipConstInApp_3423_ = _args[5];
lean_object* v_skipInstances_3424_ = _args[6];
lean_object* v___x_3425_ = _args[7];
lean_object* v_inst_3426_ = _args[8];
lean_object* v_R_3427_ = _args[9];
lean_object* v_a_3428_ = _args[10];
lean_object* v_b_3429_ = _args[11];
lean_object* v_c_3430_ = _args[12];
lean_object* v___y_3431_ = _args[13];
lean_object* v___y_3432_ = _args[14];
lean_object* v___y_3433_ = _args[15];
lean_object* v___y_3434_ = _args[16];
lean_object* v___y_3435_ = _args[17];
lean_object* v___y_3436_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_3437_; uint8_t v_skipConstInApp_boxed_3438_; uint8_t v_skipInstances_boxed_3439_; lean_object* v_res_3440_; 
v_usedLetOnly_boxed_3437_ = lean_unbox(v_usedLetOnly_3422_);
v_skipConstInApp_boxed_3438_ = lean_unbox(v_skipConstInApp_3423_);
v_skipInstances_boxed_3439_ = lean_unbox(v_skipInstances_3424_);
v_res_3440_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6(v_upperBound_3418_, v___x_3419_, v_pre_3420_, v_post_3421_, v_usedLetOnly_boxed_3437_, v_skipConstInApp_boxed_3438_, v_skipInstances_boxed_3439_, v___x_3425_, v_inst_3426_, v_R_3427_, v_a_3428_, v_b_3429_, v_c_3430_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_);
lean_dec(v___y_3435_);
lean_dec_ref(v___y_3434_);
lean_dec(v___y_3433_);
lean_dec_ref(v___y_3432_);
lean_dec(v___y_3431_);
lean_dec(v___x_3425_);
lean_dec_ref(v___x_3419_);
lean_dec(v_upperBound_3418_);
return v_res_3440_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7(lean_object* v_00_u03b2_3441_, lean_object* v_m_3442_, lean_object* v_a_3443_){
_start:
{
lean_object* v___x_3444_; 
v___x_3444_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___redArg(v_m_3442_, v_a_3443_);
return v___x_3444_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___boxed(lean_object* v_00_u03b2_3445_, lean_object* v_m_3446_, lean_object* v_a_3447_){
_start:
{
lean_object* v_res_3448_; 
v_res_3448_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7(v_00_u03b2_3445_, v_m_3446_, v_a_3447_);
lean_dec_ref(v_a_3447_);
lean_dec_ref(v_m_3446_);
return v_res_3448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10(lean_object* v_00_u03b1_3449_, lean_object* v_name_3450_, uint8_t v_bi_3451_, lean_object* v_type_3452_, lean_object* v_k_3453_, uint8_t v_kind_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_){
_start:
{
lean_object* v___x_3461_; 
v___x_3461_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg(v_name_3450_, v_bi_3451_, v_type_3452_, v_k_3453_, v_kind_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_);
return v___x_3461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___boxed(lean_object* v_00_u03b1_3462_, lean_object* v_name_3463_, lean_object* v_bi_3464_, lean_object* v_type_3465_, lean_object* v_k_3466_, lean_object* v_kind_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_){
_start:
{
uint8_t v_bi_boxed_3474_; uint8_t v_kind_boxed_3475_; lean_object* v_res_3476_; 
v_bi_boxed_3474_ = lean_unbox(v_bi_3464_);
v_kind_boxed_3475_ = lean_unbox(v_kind_3467_);
v_res_3476_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10(v_00_u03b1_3462_, v_name_3463_, v_bi_boxed_3474_, v_type_3465_, v_k_3466_, v_kind_boxed_3475_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_);
lean_dec(v___y_3472_);
lean_dec_ref(v___y_3471_);
lean_dec(v___y_3470_);
lean_dec_ref(v___y_3469_);
lean_dec(v___y_3468_);
return v_res_3476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13(lean_object* v_00_u03b1_3477_, lean_object* v_name_3478_, lean_object* v_type_3479_, lean_object* v_val_3480_, lean_object* v_k_3481_, uint8_t v_nondep_3482_, uint8_t v_kind_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_){
_start:
{
lean_object* v___x_3490_; 
v___x_3490_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13___redArg(v_name_3478_, v_type_3479_, v_val_3480_, v_k_3481_, v_nondep_3482_, v_kind_3483_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_);
return v___x_3490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13___boxed(lean_object* v_00_u03b1_3491_, lean_object* v_name_3492_, lean_object* v_type_3493_, lean_object* v_val_3494_, lean_object* v_k_3495_, lean_object* v_nondep_3496_, lean_object* v_kind_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_){
_start:
{
uint8_t v_nondep_boxed_3504_; uint8_t v_kind_boxed_3505_; lean_object* v_res_3506_; 
v_nondep_boxed_3504_ = lean_unbox(v_nondep_3496_);
v_kind_boxed_3505_ = lean_unbox(v_kind_3497_);
v_res_3506_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13(v_00_u03b1_3491_, v_name_3492_, v_type_3493_, v_val_3494_, v_k_3495_, v_nondep_boxed_3504_, v_kind_boxed_3505_, v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_);
lean_dec(v___y_3502_);
lean_dec_ref(v___y_3501_);
lean_dec(v___y_3500_);
lean_dec_ref(v___y_3499_);
lean_dec(v___y_3498_);
return v_res_3506_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16(lean_object* v_00_u03b1_3507_, lean_object* v_ref_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_){
_start:
{
lean_object* v___x_3514_; 
v___x_3514_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg(v_ref_3508_);
return v___x_3514_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___boxed(lean_object* v_00_u03b1_3515_, lean_object* v_ref_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_){
_start:
{
lean_object* v_res_3522_; 
v_res_3522_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16(v_00_u03b1_3515_, v_ref_3516_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_);
lean_dec(v___y_3520_);
lean_dec_ref(v___y_3519_);
lean_dec(v___y_3518_);
lean_dec_ref(v___y_3517_);
return v_res_3522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12(lean_object* v_00_u03b1_3523_, lean_object* v_x_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_){
_start:
{
lean_object* v___x_3531_; 
lean_inc_ref(v___y_3528_);
v___x_3531_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12___redArg(v_x_3524_, v___y_3525_, v___y_3526_, v___y_3527_, v___y_3528_, v___y_3529_);
return v___x_3531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12___boxed(lean_object* v_00_u03b1_3532_, lean_object* v_x_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_){
_start:
{
lean_object* v_res_3540_; 
v_res_3540_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12(v_00_u03b1_3532_, v_x_3533_, v___y_3534_, v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_);
lean_dec(v___y_3538_);
lean_dec_ref(v___y_3537_);
lean_dec(v___y_3536_);
lean_dec_ref(v___y_3535_);
lean_dec(v___y_3534_);
return v_res_3540_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13(lean_object* v_00_u03b2_3541_, lean_object* v_m_3542_, lean_object* v_a_3543_, lean_object* v_b_3544_){
_start:
{
lean_object* v___x_3545_; 
v___x_3545_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13___redArg(v_m_3542_, v_a_3543_, v_b_3544_);
return v___x_3545_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7_spec__8(lean_object* v_00_u03b2_3546_, lean_object* v_a_3547_, lean_object* v_x_3548_){
_start:
{
lean_object* v___x_3549_; 
v___x_3549_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7_spec__8___redArg(v_a_3547_, v_x_3548_);
return v___x_3549_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7_spec__8___boxed(lean_object* v_00_u03b2_3550_, lean_object* v_a_3551_, lean_object* v_x_3552_){
_start:
{
lean_object* v_res_3553_; 
v_res_3553_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7_spec__8(v_00_u03b2_3550_, v_a_3551_, v_x_3552_);
lean_dec(v_x_3552_);
lean_dec_ref(v_a_3551_);
return v_res_3553_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18(lean_object* v_00_u03b2_3554_, lean_object* v_a_3555_, lean_object* v_x_3556_){
_start:
{
uint8_t v___x_3557_; 
v___x_3557_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18___redArg(v_a_3555_, v_x_3556_);
return v___x_3557_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18___boxed(lean_object* v_00_u03b2_3558_, lean_object* v_a_3559_, lean_object* v_x_3560_){
_start:
{
uint8_t v_res_3561_; lean_object* v_r_3562_; 
v_res_3561_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18(v_00_u03b2_3558_, v_a_3559_, v_x_3560_);
lean_dec(v_x_3560_);
lean_dec_ref(v_a_3559_);
v_r_3562_ = lean_box(v_res_3561_);
return v_r_3562_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19(lean_object* v_00_u03b2_3563_, lean_object* v_data_3564_){
_start:
{
lean_object* v___x_3565_; 
v___x_3565_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19___redArg(v_data_3564_);
return v___x_3565_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__20(lean_object* v_00_u03b2_3566_, lean_object* v_a_3567_, lean_object* v_b_3568_, lean_object* v_x_3569_){
_start:
{
lean_object* v___x_3570_; 
v___x_3570_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__20___redArg(v_a_3567_, v_b_3568_, v_x_3569_);
return v___x_3570_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19_spec__20(lean_object* v_00_u03b2_3571_, lean_object* v_i_3572_, lean_object* v_source_3573_, lean_object* v_target_3574_){
_start:
{
lean_object* v___x_3575_; 
v___x_3575_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19_spec__20___redArg(v_i_3572_, v_source_3573_, v_target_3574_);
return v___x_3575_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19_spec__20_spec__21(lean_object* v_00_u03b2_3576_, lean_object* v_x_3577_, lean_object* v_x_3578_){
_start:
{
lean_object* v___x_3579_; 
v___x_3579_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19_spec__20_spec__21___redArg(v_x_3577_, v_x_3578_);
return v___x_3579_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_WF_preprocess_spec__1(lean_object* v_opts_3580_, lean_object* v_opt_3581_){
_start:
{
lean_object* v_name_3582_; lean_object* v_defValue_3583_; lean_object* v_map_3584_; lean_object* v___x_3585_; 
v_name_3582_ = lean_ctor_get(v_opt_3581_, 0);
v_defValue_3583_ = lean_ctor_get(v_opt_3581_, 1);
v_map_3584_ = lean_ctor_get(v_opts_3580_, 0);
v___x_3585_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3584_, v_name_3582_);
if (lean_obj_tag(v___x_3585_) == 0)
{
uint8_t v___x_3586_; 
v___x_3586_ = lean_unbox(v_defValue_3583_);
return v___x_3586_;
}
else
{
lean_object* v_val_3587_; 
v_val_3587_ = lean_ctor_get(v___x_3585_, 0);
lean_inc(v_val_3587_);
lean_dec_ref(v___x_3585_);
if (lean_obj_tag(v_val_3587_) == 1)
{
uint8_t v_v_3588_; 
v_v_3588_ = lean_ctor_get_uint8(v_val_3587_, 0);
lean_dec_ref(v_val_3587_);
return v_v_3588_;
}
else
{
uint8_t v___x_3589_; 
lean_dec(v_val_3587_);
v___x_3589_ = lean_unbox(v_defValue_3583_);
return v___x_3589_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_WF_preprocess_spec__1___boxed(lean_object* v_opts_3590_, lean_object* v_opt_3591_){
_start:
{
uint8_t v_res_3592_; lean_object* v_r_3593_; 
v_res_3592_ = l_Lean_Option_get___at___00Lean_Elab_WF_preprocess_spec__1(v_opts_3590_, v_opt_3591_);
lean_dec_ref(v_opt_3591_);
lean_dec_ref(v_opts_3590_);
v_r_3593_ = lean_box(v_res_3592_);
return v_r_3593_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___closed__0(void){
_start:
{
lean_object* v___x_3594_; 
v___x_3594_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3594_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___closed__1(void){
_start:
{
lean_object* v___x_3595_; lean_object* v___x_3596_; 
v___x_3595_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___closed__0);
v___x_3596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3596_, 0, v___x_3595_);
return v___x_3596_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3(lean_object* v_00_u03b2_3597_){
_start:
{
lean_object* v___x_3598_; 
v___x_3598_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___closed__1);
return v___x_3598_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_WF_preprocess_spec__5___redArg(lean_object* v_cls_3602_, lean_object* v___y_3603_){
_start:
{
lean_object* v_options_3605_; uint8_t v_hasTrace_3606_; 
v_options_3605_ = lean_ctor_get(v___y_3603_, 2);
v_hasTrace_3606_ = lean_ctor_get_uint8(v_options_3605_, sizeof(void*)*1);
if (v_hasTrace_3606_ == 0)
{
lean_object* v___x_3607_; lean_object* v___x_3608_; 
lean_dec(v_cls_3602_);
v___x_3607_ = lean_box(v_hasTrace_3606_);
v___x_3608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3608_, 0, v___x_3607_);
return v___x_3608_;
}
else
{
lean_object* v_inheritedTraceOptions_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; uint8_t v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; 
v_inheritedTraceOptions_3609_ = lean_ctor_get(v___y_3603_, 13);
v___x_3610_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Elab_WF_preprocess_spec__5___redArg___closed__1));
v___x_3611_ = l_Lean_Name_append(v___x_3610_, v_cls_3602_);
v___x_3612_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3609_, v_options_3605_, v___x_3611_);
lean_dec(v___x_3611_);
v___x_3613_ = lean_box(v___x_3612_);
v___x_3614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3614_, 0, v___x_3613_);
return v___x_3614_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_WF_preprocess_spec__5___redArg___boxed(lean_object* v_cls_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_){
_start:
{
lean_object* v_res_3618_; 
v_res_3618_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_WF_preprocess_spec__5___redArg(v_cls_3615_, v___y_3616_);
lean_dec_ref(v___y_3616_);
return v_res_3618_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_WF_preprocess_spec__5(lean_object* v_cls_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_){
_start:
{
lean_object* v___x_3625_; 
v___x_3625_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_WF_preprocess_spec__5___redArg(v_cls_3619_, v___y_3622_);
return v___x_3625_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_WF_preprocess_spec__5___boxed(lean_object* v_cls_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_){
_start:
{
lean_object* v_res_3632_; 
v_res_3632_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_WF_preprocess_spec__5(v_cls_3626_, v___y_3627_, v___y_3628_, v___y_3629_, v___y_3630_);
lean_dec(v___y_3630_);
lean_dec_ref(v___y_3629_);
lean_dec(v___y_3628_);
lean_dec_ref(v___y_3627_);
return v_res_3632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__7___redArg(lean_object* v_e_3633_, lean_object* v_k_3634_, uint8_t v_cleanupAnnotations_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_){
_start:
{
lean_object* v___f_3641_; uint8_t v___x_3642_; uint8_t v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; 
v___f_3641_ = lean_alloc_closure((void*)(l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3641_, 0, v_k_3634_);
v___x_3642_ = 1;
v___x_3643_ = 0;
v___x_3644_ = lean_box(0);
v___x_3645_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_3633_, v___x_3642_, v___x_3643_, v___x_3642_, v___x_3643_, v___x_3644_, v___f_3641_, v_cleanupAnnotations_3635_, v___y_3636_, v___y_3637_, v___y_3638_, v___y_3639_);
if (lean_obj_tag(v___x_3645_) == 0)
{
lean_object* v_a_3646_; lean_object* v___x_3648_; uint8_t v_isShared_3649_; uint8_t v_isSharedCheck_3653_; 
v_a_3646_ = lean_ctor_get(v___x_3645_, 0);
v_isSharedCheck_3653_ = !lean_is_exclusive(v___x_3645_);
if (v_isSharedCheck_3653_ == 0)
{
v___x_3648_ = v___x_3645_;
v_isShared_3649_ = v_isSharedCheck_3653_;
goto v_resetjp_3647_;
}
else
{
lean_inc(v_a_3646_);
lean_dec(v___x_3645_);
v___x_3648_ = lean_box(0);
v_isShared_3649_ = v_isSharedCheck_3653_;
goto v_resetjp_3647_;
}
v_resetjp_3647_:
{
lean_object* v___x_3651_; 
if (v_isShared_3649_ == 0)
{
v___x_3651_ = v___x_3648_;
goto v_reusejp_3650_;
}
else
{
lean_object* v_reuseFailAlloc_3652_; 
v_reuseFailAlloc_3652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3652_, 0, v_a_3646_);
v___x_3651_ = v_reuseFailAlloc_3652_;
goto v_reusejp_3650_;
}
v_reusejp_3650_:
{
return v___x_3651_;
}
}
}
else
{
lean_object* v_a_3654_; lean_object* v___x_3656_; uint8_t v_isShared_3657_; uint8_t v_isSharedCheck_3661_; 
v_a_3654_ = lean_ctor_get(v___x_3645_, 0);
v_isSharedCheck_3661_ = !lean_is_exclusive(v___x_3645_);
if (v_isSharedCheck_3661_ == 0)
{
v___x_3656_ = v___x_3645_;
v_isShared_3657_ = v_isSharedCheck_3661_;
goto v_resetjp_3655_;
}
else
{
lean_inc(v_a_3654_);
lean_dec(v___x_3645_);
v___x_3656_ = lean_box(0);
v_isShared_3657_ = v_isSharedCheck_3661_;
goto v_resetjp_3655_;
}
v_resetjp_3655_:
{
lean_object* v___x_3659_; 
if (v_isShared_3657_ == 0)
{
v___x_3659_ = v___x_3656_;
goto v_reusejp_3658_;
}
else
{
lean_object* v_reuseFailAlloc_3660_; 
v_reuseFailAlloc_3660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3660_, 0, v_a_3654_);
v___x_3659_ = v_reuseFailAlloc_3660_;
goto v_reusejp_3658_;
}
v_reusejp_3658_:
{
return v___x_3659_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__7___redArg___boxed(lean_object* v_e_3662_, lean_object* v_k_3663_, lean_object* v_cleanupAnnotations_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3670_; lean_object* v_res_3671_; 
v_cleanupAnnotations_boxed_3670_ = lean_unbox(v_cleanupAnnotations_3664_);
v_res_3671_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__7___redArg(v_e_3662_, v_k_3663_, v_cleanupAnnotations_boxed_3670_, v___y_3665_, v___y_3666_, v___y_3667_, v___y_3668_);
lean_dec(v___y_3668_);
lean_dec_ref(v___y_3667_);
lean_dec(v___y_3666_);
lean_dec_ref(v___y_3665_);
return v_res_3671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__7(lean_object* v_00_u03b1_3672_, lean_object* v_e_3673_, lean_object* v_k_3674_, uint8_t v_cleanupAnnotations_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_){
_start:
{
lean_object* v___x_3681_; 
v___x_3681_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__7___redArg(v_e_3673_, v_k_3674_, v_cleanupAnnotations_3675_, v___y_3676_, v___y_3677_, v___y_3678_, v___y_3679_);
return v___x_3681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__7___boxed(lean_object* v_00_u03b1_3682_, lean_object* v_e_3683_, lean_object* v_k_3684_, lean_object* v_cleanupAnnotations_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3691_; lean_object* v_res_3692_; 
v_cleanupAnnotations_boxed_3691_ = lean_unbox(v_cleanupAnnotations_3685_);
v_res_3692_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__7(v_00_u03b1_3682_, v_e_3683_, v_k_3684_, v_cleanupAnnotations_boxed_3691_, v___y_3686_, v___y_3687_, v___y_3688_, v___y_3689_);
lean_dec(v___y_3689_);
lean_dec_ref(v___y_3688_);
lean_dec(v___y_3687_);
lean_dec_ref(v___y_3686_);
return v_res_3692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0___redArg(lean_object* v_x_3693_, lean_object* v_x_3694_, lean_object* v_x_3695_){
_start:
{
if (lean_obj_tag(v_x_3693_) == 5)
{
lean_object* v_fn_3700_; lean_object* v_arg_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; 
v_fn_3700_ = lean_ctor_get(v_x_3693_, 0);
lean_inc_ref(v_fn_3700_);
v_arg_3701_ = lean_ctor_get(v_x_3693_, 1);
lean_inc_ref(v_arg_3701_);
lean_dec_ref(v_x_3693_);
v___x_3702_ = lean_array_set(v_x_3694_, v_x_3695_, v_arg_3701_);
v___x_3703_ = lean_unsigned_to_nat(1u);
v___x_3704_ = lean_nat_sub(v_x_3695_, v___x_3703_);
lean_dec(v_x_3695_);
v_x_3693_ = v_fn_3700_;
v_x_3694_ = v___x_3702_;
v_x_3695_ = v___x_3704_;
goto _start;
}
else
{
lean_object* v___x_3706_; uint8_t v___x_3707_; 
lean_dec(v_x_3695_);
v___x_3706_ = ((lean_object*)(l_Lean_Elab_WF_isWfParam_x3f___closed__1));
v___x_3707_ = l_Lean_Expr_isConstOf(v_x_3693_, v___x_3706_);
lean_dec_ref(v_x_3693_);
if (v___x_3707_ == 0)
{
lean_dec_ref(v_x_3694_);
goto v___jp_3697_;
}
else
{
lean_object* v___x_3708_; lean_object* v___x_3709_; uint8_t v___x_3710_; 
v___x_3708_ = lean_unsigned_to_nat(2u);
v___x_3709_ = lean_array_get_size(v_x_3694_);
v___x_3710_ = lean_nat_dec_le(v___x_3708_, v___x_3709_);
if (v___x_3710_ == 0)
{
lean_dec_ref(v_x_3694_);
goto v___jp_3697_;
}
else
{
lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; 
v___x_3711_ = lean_unsigned_to_nat(1u);
v___x_3712_ = lean_array_fget(v_x_3694_, v___x_3711_);
v___x_3713_ = l_Array_toSubarray___redArg(v_x_3694_, v___x_3708_, v___x_3709_);
v___x_3714_ = l_Subarray_copy___redArg(v___x_3713_);
v___x_3715_ = l_Lean_mkAppN(v___x_3712_, v___x_3714_);
lean_dec_ref(v___x_3714_);
v___x_3716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3716_, 0, v___x_3715_);
v___x_3717_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3717_, 0, v___x_3716_);
v___x_3718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3718_, 0, v___x_3717_);
return v___x_3718_;
}
}
}
v___jp_3697_:
{
lean_object* v___x_3698_; lean_object* v___x_3699_; 
v___x_3698_ = ((lean_object*)(l_Lean_Elab_WF_paramProj___closed__0));
v___x_3699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3699_, 0, v___x_3698_);
return v___x_3699_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0___redArg___boxed(lean_object* v_x_3719_, lean_object* v_x_3720_, lean_object* v_x_3721_, lean_object* v___y_3722_){
_start:
{
lean_object* v_res_3723_; 
v_res_3723_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0___redArg(v_x_3719_, v_x_3720_, v_x_3721_);
return v_res_3723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preprocess___lam__1(lean_object* v_e_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_){
_start:
{
lean_object* v_dummy_3730_; lean_object* v_nargs_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; 
v_dummy_3730_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0);
v_nargs_3731_ = l_Lean_Expr_getAppNumArgs(v_e_3724_);
lean_inc(v_nargs_3731_);
v___x_3732_ = lean_mk_array(v_nargs_3731_, v_dummy_3730_);
v___x_3733_ = lean_unsigned_to_nat(1u);
v___x_3734_ = lean_nat_sub(v_nargs_3731_, v___x_3733_);
lean_dec(v_nargs_3731_);
v___x_3735_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0___redArg(v_e_3724_, v___x_3732_, v___x_3734_);
return v___x_3735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preprocess___lam__1___boxed(lean_object* v_e_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_){
_start:
{
lean_object* v_res_3742_; 
v_res_3742_ = l_Lean_Elab_WF_preprocess___lam__1(v_e_3736_, v___y_3737_, v___y_3738_, v___y_3739_, v___y_3740_);
lean_dec(v___y_3740_);
lean_dec_ref(v___y_3739_);
lean_dec(v___y_3738_);
lean_dec_ref(v___y_3737_);
return v_res_3742_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__10_spec__12___redArg(lean_object* v_ref_3743_){
_start:
{
lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; 
v___x_3745_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__5);
v___x_3746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3746_, 0, v_ref_3743_);
lean_ctor_set(v___x_3746_, 1, v___x_3745_);
v___x_3747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3747_, 0, v___x_3746_);
return v___x_3747_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__10_spec__12___redArg___boxed(lean_object* v_ref_3748_, lean_object* v___y_3749_){
_start:
{
lean_object* v_res_3750_; 
v_res_3750_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__10_spec__12___redArg(v_ref_3748_);
return v_res_3750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__10___redArg(lean_object* v_x_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_){
_start:
{
lean_object* v___y_3759_; lean_object* v_fileName_3768_; lean_object* v_fileMap_3769_; lean_object* v_options_3770_; lean_object* v_currRecDepth_3771_; lean_object* v_maxRecDepth_3772_; lean_object* v_ref_3773_; lean_object* v_currNamespace_3774_; lean_object* v_openDecls_3775_; lean_object* v_initHeartbeats_3776_; lean_object* v_maxHeartbeats_3777_; lean_object* v_quotContext_3778_; lean_object* v_currMacroScope_3779_; uint8_t v_diag_3780_; lean_object* v_cancelTk_x3f_3781_; uint8_t v_suppressElabErrors_3782_; lean_object* v_inheritedTraceOptions_3783_; uint8_t v___x_3784_; 
v_fileName_3768_ = lean_ctor_get(v___y_3755_, 0);
lean_inc_ref(v_fileName_3768_);
v_fileMap_3769_ = lean_ctor_get(v___y_3755_, 1);
lean_inc_ref(v_fileMap_3769_);
v_options_3770_ = lean_ctor_get(v___y_3755_, 2);
lean_inc_ref(v_options_3770_);
v_currRecDepth_3771_ = lean_ctor_get(v___y_3755_, 3);
lean_inc(v_currRecDepth_3771_);
v_maxRecDepth_3772_ = lean_ctor_get(v___y_3755_, 4);
lean_inc(v_maxRecDepth_3772_);
v_ref_3773_ = lean_ctor_get(v___y_3755_, 5);
lean_inc(v_ref_3773_);
v_currNamespace_3774_ = lean_ctor_get(v___y_3755_, 6);
lean_inc(v_currNamespace_3774_);
v_openDecls_3775_ = lean_ctor_get(v___y_3755_, 7);
lean_inc(v_openDecls_3775_);
v_initHeartbeats_3776_ = lean_ctor_get(v___y_3755_, 8);
lean_inc(v_initHeartbeats_3776_);
v_maxHeartbeats_3777_ = lean_ctor_get(v___y_3755_, 9);
lean_inc(v_maxHeartbeats_3777_);
v_quotContext_3778_ = lean_ctor_get(v___y_3755_, 10);
lean_inc(v_quotContext_3778_);
v_currMacroScope_3779_ = lean_ctor_get(v___y_3755_, 11);
lean_inc(v_currMacroScope_3779_);
v_diag_3780_ = lean_ctor_get_uint8(v___y_3755_, sizeof(void*)*14);
v_cancelTk_x3f_3781_ = lean_ctor_get(v___y_3755_, 12);
lean_inc(v_cancelTk_x3f_3781_);
v_suppressElabErrors_3782_ = lean_ctor_get_uint8(v___y_3755_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3783_ = lean_ctor_get(v___y_3755_, 13);
lean_inc_ref(v_inheritedTraceOptions_3783_);
lean_dec_ref(v___y_3755_);
v___x_3784_ = lean_nat_dec_eq(v_currRecDepth_3771_, v_maxRecDepth_3772_);
if (v___x_3784_ == 0)
{
lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; 
v___x_3785_ = lean_unsigned_to_nat(1u);
v___x_3786_ = lean_nat_add(v_currRecDepth_3771_, v___x_3785_);
lean_dec(v_currRecDepth_3771_);
v___x_3787_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3787_, 0, v_fileName_3768_);
lean_ctor_set(v___x_3787_, 1, v_fileMap_3769_);
lean_ctor_set(v___x_3787_, 2, v_options_3770_);
lean_ctor_set(v___x_3787_, 3, v___x_3786_);
lean_ctor_set(v___x_3787_, 4, v_maxRecDepth_3772_);
lean_ctor_set(v___x_3787_, 5, v_ref_3773_);
lean_ctor_set(v___x_3787_, 6, v_currNamespace_3774_);
lean_ctor_set(v___x_3787_, 7, v_openDecls_3775_);
lean_ctor_set(v___x_3787_, 8, v_initHeartbeats_3776_);
lean_ctor_set(v___x_3787_, 9, v_maxHeartbeats_3777_);
lean_ctor_set(v___x_3787_, 10, v_quotContext_3778_);
lean_ctor_set(v___x_3787_, 11, v_currMacroScope_3779_);
lean_ctor_set(v___x_3787_, 12, v_cancelTk_x3f_3781_);
lean_ctor_set(v___x_3787_, 13, v_inheritedTraceOptions_3783_);
lean_ctor_set_uint8(v___x_3787_, sizeof(void*)*14, v_diag_3780_);
lean_ctor_set_uint8(v___x_3787_, sizeof(void*)*14 + 1, v_suppressElabErrors_3782_);
lean_inc(v___y_3756_);
lean_inc(v___y_3754_);
lean_inc_ref(v___y_3753_);
lean_inc(v___y_3752_);
v___x_3788_ = lean_apply_6(v_x_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___x_3787_, v___y_3756_, lean_box(0));
v___y_3759_ = v___x_3788_;
goto v___jp_3758_;
}
else
{
lean_object* v___x_3789_; 
lean_dec_ref(v_inheritedTraceOptions_3783_);
lean_dec(v_cancelTk_x3f_3781_);
lean_dec(v_currMacroScope_3779_);
lean_dec(v_quotContext_3778_);
lean_dec(v_maxHeartbeats_3777_);
lean_dec(v_initHeartbeats_3776_);
lean_dec(v_openDecls_3775_);
lean_dec(v_currNamespace_3774_);
lean_dec(v_maxRecDepth_3772_);
lean_dec(v_currRecDepth_3771_);
lean_dec_ref(v_options_3770_);
lean_dec_ref(v_fileMap_3769_);
lean_dec_ref(v_fileName_3768_);
lean_dec_ref(v_x_3751_);
v___x_3789_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__10_spec__12___redArg(v_ref_3773_);
v___y_3759_ = v___x_3789_;
goto v___jp_3758_;
}
v___jp_3758_:
{
if (lean_obj_tag(v___y_3759_) == 0)
{
return v___y_3759_;
}
else
{
lean_object* v_a_3760_; lean_object* v___x_3762_; uint8_t v_isShared_3763_; uint8_t v_isSharedCheck_3767_; 
v_a_3760_ = lean_ctor_get(v___y_3759_, 0);
v_isSharedCheck_3767_ = !lean_is_exclusive(v___y_3759_);
if (v_isSharedCheck_3767_ == 0)
{
v___x_3762_ = v___y_3759_;
v_isShared_3763_ = v_isSharedCheck_3767_;
goto v_resetjp_3761_;
}
else
{
lean_inc(v_a_3760_);
lean_dec(v___y_3759_);
v___x_3762_ = lean_box(0);
v_isShared_3763_ = v_isSharedCheck_3767_;
goto v_resetjp_3761_;
}
v_resetjp_3761_:
{
lean_object* v___x_3765_; 
if (v_isShared_3763_ == 0)
{
v___x_3765_ = v___x_3762_;
goto v_reusejp_3764_;
}
else
{
lean_object* v_reuseFailAlloc_3766_; 
v_reuseFailAlloc_3766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3766_, 0, v_a_3760_);
v___x_3765_ = v_reuseFailAlloc_3766_;
goto v_reusejp_3764_;
}
v_reusejp_3764_:
{
return v___x_3765_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__10___redArg___boxed(lean_object* v_x_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_){
_start:
{
lean_object* v_res_3797_; 
v_res_3797_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__10___redArg(v_x_3790_, v___y_3791_, v___y_3792_, v___y_3793_, v___y_3794_, v___y_3795_);
lean_dec(v___y_3795_);
lean_dec(v___y_3793_);
lean_dec_ref(v___y_3792_);
lean_dec(v___y_3791_);
return v_res_3797_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(lean_object* v_pre_3798_, lean_object* v_post_3799_, size_t v_sz_3800_, size_t v_i_3801_, lean_object* v_bs_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_){
_start:
{
uint8_t v___x_3809_; 
v___x_3809_ = lean_usize_dec_lt(v_i_3801_, v_sz_3800_);
if (v___x_3809_ == 0)
{
lean_object* v___x_3810_; 
lean_dec_ref(v_post_3799_);
lean_dec_ref(v_pre_3798_);
v___x_3810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3810_, 0, v_bs_3802_);
return v___x_3810_;
}
else
{
lean_object* v_v_3811_; lean_object* v___x_3812_; 
v_v_3811_ = lean_array_uget_borrowed(v_bs_3802_, v_i_3801_);
lean_inc(v_v_3811_);
lean_inc_ref(v_post_3799_);
lean_inc_ref(v_pre_3798_);
v___x_3812_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3798_, v_post_3799_, v_v_3811_, v___y_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_);
if (lean_obj_tag(v___x_3812_) == 0)
{
lean_object* v_a_3813_; lean_object* v___x_3814_; lean_object* v_bs_x27_3815_; size_t v___x_3816_; size_t v___x_3817_; lean_object* v___x_3818_; 
v_a_3813_ = lean_ctor_get(v___x_3812_, 0);
lean_inc(v_a_3813_);
lean_dec_ref(v___x_3812_);
v___x_3814_ = lean_unsigned_to_nat(0u);
v_bs_x27_3815_ = lean_array_uset(v_bs_3802_, v_i_3801_, v___x_3814_);
v___x_3816_ = ((size_t)1ULL);
v___x_3817_ = lean_usize_add(v_i_3801_, v___x_3816_);
v___x_3818_ = lean_array_uset(v_bs_x27_3815_, v_i_3801_, v_a_3813_);
v_i_3801_ = v___x_3817_;
v_bs_3802_ = v___x_3818_;
goto _start;
}
else
{
lean_object* v_a_3820_; lean_object* v___x_3822_; uint8_t v_isShared_3823_; uint8_t v_isSharedCheck_3827_; 
lean_dec_ref(v_bs_3802_);
lean_dec_ref(v_post_3799_);
lean_dec_ref(v_pre_3798_);
v_a_3820_ = lean_ctor_get(v___x_3812_, 0);
v_isSharedCheck_3827_ = !lean_is_exclusive(v___x_3812_);
if (v_isSharedCheck_3827_ == 0)
{
v___x_3822_ = v___x_3812_;
v_isShared_3823_ = v_isSharedCheck_3827_;
goto v_resetjp_3821_;
}
else
{
lean_inc(v_a_3820_);
lean_dec(v___x_3812_);
v___x_3822_ = lean_box(0);
v_isShared_3823_ = v_isSharedCheck_3827_;
goto v_resetjp_3821_;
}
v_resetjp_3821_:
{
lean_object* v___x_3825_; 
if (v_isShared_3823_ == 0)
{
v___x_3825_ = v___x_3822_;
goto v_reusejp_3824_;
}
else
{
lean_object* v_reuseFailAlloc_3826_; 
v_reuseFailAlloc_3826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3826_, 0, v_a_3820_);
v___x_3825_ = v_reuseFailAlloc_3826_;
goto v_reusejp_3824_;
}
v_reusejp_3824_:
{
return v___x_3825_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9(lean_object* v_pre_3828_, lean_object* v_post_3829_, lean_object* v_x_3830_, lean_object* v_x_3831_, lean_object* v_x_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_){
_start:
{
if (lean_obj_tag(v_x_3830_) == 5)
{
lean_object* v_fn_3839_; lean_object* v_arg_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; 
v_fn_3839_ = lean_ctor_get(v_x_3830_, 0);
lean_inc_ref(v_fn_3839_);
v_arg_3840_ = lean_ctor_get(v_x_3830_, 1);
lean_inc_ref(v_arg_3840_);
lean_dec_ref(v_x_3830_);
v___x_3841_ = lean_array_set(v_x_3831_, v_x_3832_, v_arg_3840_);
v___x_3842_ = lean_unsigned_to_nat(1u);
v___x_3843_ = lean_nat_sub(v_x_3832_, v___x_3842_);
lean_dec(v_x_3832_);
v_x_3830_ = v_fn_3839_;
v_x_3831_ = v___x_3841_;
v_x_3832_ = v___x_3843_;
goto _start;
}
else
{
lean_object* v___x_3845_; 
lean_dec(v_x_3832_);
lean_inc_ref(v_post_3829_);
lean_inc_ref(v_pre_3828_);
v___x_3845_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3828_, v_post_3829_, v_x_3830_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_);
if (lean_obj_tag(v___x_3845_) == 0)
{
lean_object* v_a_3846_; size_t v_sz_3847_; size_t v___x_3848_; lean_object* v___x_3849_; 
v_a_3846_ = lean_ctor_get(v___x_3845_, 0);
lean_inc(v_a_3846_);
lean_dec_ref(v___x_3845_);
v_sz_3847_ = lean_array_size(v_x_3831_);
v___x_3848_ = ((size_t)0ULL);
lean_inc_ref(v_post_3829_);
lean_inc_ref(v_pre_3828_);
v___x_3849_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3828_, v_post_3829_, v_sz_3847_, v___x_3848_, v_x_3831_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_);
if (lean_obj_tag(v___x_3849_) == 0)
{
lean_object* v_a_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; 
v_a_3850_ = lean_ctor_get(v___x_3849_, 0);
lean_inc(v_a_3850_);
lean_dec_ref(v___x_3849_);
v___x_3851_ = l_Lean_mkAppN(v_a_3846_, v_a_3850_);
lean_dec(v_a_3850_);
v___x_3852_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__8(v_pre_3828_, v_post_3829_, v___x_3851_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_);
return v___x_3852_;
}
else
{
lean_object* v_a_3853_; lean_object* v___x_3855_; uint8_t v_isShared_3856_; uint8_t v_isSharedCheck_3860_; 
lean_dec(v_a_3846_);
lean_dec_ref(v_post_3829_);
lean_dec_ref(v_pre_3828_);
v_a_3853_ = lean_ctor_get(v___x_3849_, 0);
v_isSharedCheck_3860_ = !lean_is_exclusive(v___x_3849_);
if (v_isSharedCheck_3860_ == 0)
{
v___x_3855_ = v___x_3849_;
v_isShared_3856_ = v_isSharedCheck_3860_;
goto v_resetjp_3854_;
}
else
{
lean_inc(v_a_3853_);
lean_dec(v___x_3849_);
v___x_3855_ = lean_box(0);
v_isShared_3856_ = v_isSharedCheck_3860_;
goto v_resetjp_3854_;
}
v_resetjp_3854_:
{
lean_object* v___x_3858_; 
if (v_isShared_3856_ == 0)
{
v___x_3858_ = v___x_3855_;
goto v_reusejp_3857_;
}
else
{
lean_object* v_reuseFailAlloc_3859_; 
v_reuseFailAlloc_3859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3859_, 0, v_a_3853_);
v___x_3858_ = v_reuseFailAlloc_3859_;
goto v_reusejp_3857_;
}
v_reusejp_3857_:
{
return v___x_3858_;
}
}
}
}
else
{
lean_dec_ref(v_x_3831_);
lean_dec_ref(v_post_3829_);
lean_dec_ref(v_pre_3828_);
return v___x_3845_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4___lam__1(lean_object* v_pre_3861_, lean_object* v_e_3862_, lean_object* v_post_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_){
_start:
{
uint8_t v___y_3871_; lean_object* v___y_3872_; lean_object* v___y_3873_; lean_object* v___y_3874_; lean_object* v___y_3875_; lean_object* v___y_3876_; lean_object* v___y_3877_; uint8_t v___y_3878_; lean_object* v___y_3888_; lean_object* v___y_3889_; lean_object* v___y_3890_; lean_object* v___y_3891_; uint8_t v___y_3892_; uint8_t v___y_3893_; lean_object* v___y_3901_; lean_object* v___y_3902_; lean_object* v___y_3903_; uint8_t v___y_3904_; lean_object* v___y_3905_; uint8_t v___y_3906_; lean_object* v___x_3913_; 
lean_inc_ref(v_pre_3861_);
lean_inc(v___y_3868_);
lean_inc_ref(v___y_3867_);
lean_inc(v___y_3866_);
lean_inc_ref(v___y_3865_);
lean_inc_ref(v_e_3862_);
v___x_3913_ = lean_apply_6(v_pre_3861_, v_e_3862_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_, lean_box(0));
if (lean_obj_tag(v___x_3913_) == 0)
{
lean_object* v_a_3914_; lean_object* v___x_3916_; uint8_t v_isShared_3917_; uint8_t v_isSharedCheck_4003_; 
v_a_3914_ = lean_ctor_get(v___x_3913_, 0);
v_isSharedCheck_4003_ = !lean_is_exclusive(v___x_3913_);
if (v_isSharedCheck_4003_ == 0)
{
v___x_3916_ = v___x_3913_;
v_isShared_3917_ = v_isSharedCheck_4003_;
goto v_resetjp_3915_;
}
else
{
lean_inc(v_a_3914_);
lean_dec(v___x_3913_);
v___x_3916_ = lean_box(0);
v_isShared_3917_ = v_isSharedCheck_4003_;
goto v_resetjp_3915_;
}
v_resetjp_3915_:
{
lean_object* v___y_3919_; 
switch(lean_obj_tag(v_a_3914_))
{
case 0:
{
lean_object* v_e_3993_; lean_object* v___x_3995_; 
lean_dec_ref(v_post_3863_);
lean_dec_ref(v_e_3862_);
lean_dec_ref(v_pre_3861_);
v_e_3993_ = lean_ctor_get(v_a_3914_, 0);
lean_inc_ref(v_e_3993_);
lean_dec_ref(v_a_3914_);
if (v_isShared_3917_ == 0)
{
lean_ctor_set(v___x_3916_, 0, v_e_3993_);
v___x_3995_ = v___x_3916_;
goto v_reusejp_3994_;
}
else
{
lean_object* v_reuseFailAlloc_3996_; 
v_reuseFailAlloc_3996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3996_, 0, v_e_3993_);
v___x_3995_ = v_reuseFailAlloc_3996_;
goto v_reusejp_3994_;
}
v_reusejp_3994_:
{
return v___x_3995_;
}
}
case 1:
{
lean_object* v_e_3997_; lean_object* v___x_3998_; 
lean_del_object(v___x_3916_);
lean_dec_ref(v_e_3862_);
v_e_3997_ = lean_ctor_get(v_a_3914_, 0);
lean_inc_ref(v_e_3997_);
lean_dec_ref(v_a_3914_);
lean_inc_ref(v_post_3863_);
lean_inc_ref(v_pre_3861_);
v___x_3998_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3861_, v_post_3863_, v_e_3997_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_);
if (lean_obj_tag(v___x_3998_) == 0)
{
lean_object* v_a_3999_; lean_object* v___x_4000_; 
v_a_3999_ = lean_ctor_get(v___x_3998_, 0);
lean_inc(v_a_3999_);
lean_dec_ref(v___x_3998_);
v___x_4000_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__8(v_pre_3861_, v_post_3863_, v_a_3999_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_);
return v___x_4000_;
}
else
{
lean_dec_ref(v_post_3863_);
lean_dec_ref(v_pre_3861_);
return v___x_3998_;
}
}
default: 
{
lean_object* v_e_x3f_4001_; 
lean_del_object(v___x_3916_);
v_e_x3f_4001_ = lean_ctor_get(v_a_3914_, 0);
lean_inc(v_e_x3f_4001_);
lean_dec_ref(v_a_3914_);
if (lean_obj_tag(v_e_x3f_4001_) == 0)
{
v___y_3919_ = v_e_3862_;
goto v___jp_3918_;
}
else
{
lean_object* v_val_4002_; 
lean_dec_ref(v_e_3862_);
v_val_4002_ = lean_ctor_get(v_e_x3f_4001_, 0);
lean_inc(v_val_4002_);
lean_dec_ref(v_e_x3f_4001_);
v___y_3919_ = v_val_4002_;
goto v___jp_3918_;
}
}
}
v___jp_3918_:
{
switch(lean_obj_tag(v___y_3919_))
{
case 7:
{
lean_object* v_binderName_3920_; lean_object* v_binderType_3921_; lean_object* v_body_3922_; uint8_t v_binderInfo_3923_; lean_object* v___x_3924_; 
v_binderName_3920_ = lean_ctor_get(v___y_3919_, 0);
lean_inc(v_binderName_3920_);
v_binderType_3921_ = lean_ctor_get(v___y_3919_, 1);
v_body_3922_ = lean_ctor_get(v___y_3919_, 2);
v_binderInfo_3923_ = lean_ctor_get_uint8(v___y_3919_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_3921_);
lean_inc_ref(v_post_3863_);
lean_inc_ref(v_pre_3861_);
v___x_3924_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3861_, v_post_3863_, v_binderType_3921_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_);
if (lean_obj_tag(v___x_3924_) == 0)
{
lean_object* v_a_3925_; lean_object* v___x_3926_; 
v_a_3925_ = lean_ctor_get(v___x_3924_, 0);
lean_inc(v_a_3925_);
lean_dec_ref(v___x_3924_);
lean_inc_ref(v_body_3922_);
lean_inc_ref(v_post_3863_);
lean_inc_ref(v_pre_3861_);
v___x_3926_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3861_, v_post_3863_, v_body_3922_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_);
if (lean_obj_tag(v___x_3926_) == 0)
{
lean_object* v_a_3927_; size_t v___x_3928_; size_t v___x_3929_; uint8_t v___x_3930_; 
v_a_3927_ = lean_ctor_get(v___x_3926_, 0);
lean_inc(v_a_3927_);
lean_dec_ref(v___x_3926_);
v___x_3928_ = lean_ptr_addr(v_binderType_3921_);
v___x_3929_ = lean_ptr_addr(v_a_3925_);
v___x_3930_ = lean_usize_dec_eq(v___x_3928_, v___x_3929_);
if (v___x_3930_ == 0)
{
v___y_3901_ = v_a_3927_;
v___y_3902_ = v_binderName_3920_;
v___y_3903_ = v___y_3919_;
v___y_3904_ = v_binderInfo_3923_;
v___y_3905_ = v_a_3925_;
v___y_3906_ = v___x_3930_;
goto v___jp_3900_;
}
else
{
size_t v___x_3931_; size_t v___x_3932_; uint8_t v___x_3933_; 
v___x_3931_ = lean_ptr_addr(v_body_3922_);
v___x_3932_ = lean_ptr_addr(v_a_3927_);
v___x_3933_ = lean_usize_dec_eq(v___x_3931_, v___x_3932_);
v___y_3901_ = v_a_3927_;
v___y_3902_ = v_binderName_3920_;
v___y_3903_ = v___y_3919_;
v___y_3904_ = v_binderInfo_3923_;
v___y_3905_ = v_a_3925_;
v___y_3906_ = v___x_3933_;
goto v___jp_3900_;
}
}
else
{
lean_dec(v_a_3925_);
lean_dec(v_binderName_3920_);
lean_dec_ref(v___y_3919_);
lean_dec_ref(v_post_3863_);
lean_dec_ref(v_pre_3861_);
return v___x_3926_;
}
}
else
{
lean_dec(v_binderName_3920_);
lean_dec_ref(v___y_3919_);
lean_dec_ref(v_post_3863_);
lean_dec_ref(v_pre_3861_);
return v___x_3924_;
}
}
case 6:
{
lean_object* v_binderName_3934_; lean_object* v_binderType_3935_; lean_object* v_body_3936_; uint8_t v_binderInfo_3937_; lean_object* v___x_3938_; 
v_binderName_3934_ = lean_ctor_get(v___y_3919_, 0);
lean_inc(v_binderName_3934_);
v_binderType_3935_ = lean_ctor_get(v___y_3919_, 1);
v_body_3936_ = lean_ctor_get(v___y_3919_, 2);
v_binderInfo_3937_ = lean_ctor_get_uint8(v___y_3919_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_3935_);
lean_inc_ref(v_post_3863_);
lean_inc_ref(v_pre_3861_);
v___x_3938_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3861_, v_post_3863_, v_binderType_3935_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_);
if (lean_obj_tag(v___x_3938_) == 0)
{
lean_object* v_a_3939_; lean_object* v___x_3940_; 
v_a_3939_ = lean_ctor_get(v___x_3938_, 0);
lean_inc(v_a_3939_);
lean_dec_ref(v___x_3938_);
lean_inc_ref(v_body_3936_);
lean_inc_ref(v_post_3863_);
lean_inc_ref(v_pre_3861_);
v___x_3940_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3861_, v_post_3863_, v_body_3936_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_);
if (lean_obj_tag(v___x_3940_) == 0)
{
lean_object* v_a_3941_; size_t v___x_3942_; size_t v___x_3943_; uint8_t v___x_3944_; 
v_a_3941_ = lean_ctor_get(v___x_3940_, 0);
lean_inc(v_a_3941_);
lean_dec_ref(v___x_3940_);
v___x_3942_ = lean_ptr_addr(v_binderType_3935_);
v___x_3943_ = lean_ptr_addr(v_a_3939_);
v___x_3944_ = lean_usize_dec_eq(v___x_3942_, v___x_3943_);
if (v___x_3944_ == 0)
{
v___y_3888_ = v_a_3939_;
v___y_3889_ = v___y_3919_;
v___y_3890_ = v_a_3941_;
v___y_3891_ = v_binderName_3934_;
v___y_3892_ = v_binderInfo_3937_;
v___y_3893_ = v___x_3944_;
goto v___jp_3887_;
}
else
{
size_t v___x_3945_; size_t v___x_3946_; uint8_t v___x_3947_; 
v___x_3945_ = lean_ptr_addr(v_body_3936_);
v___x_3946_ = lean_ptr_addr(v_a_3941_);
v___x_3947_ = lean_usize_dec_eq(v___x_3945_, v___x_3946_);
v___y_3888_ = v_a_3939_;
v___y_3889_ = v___y_3919_;
v___y_3890_ = v_a_3941_;
v___y_3891_ = v_binderName_3934_;
v___y_3892_ = v_binderInfo_3937_;
v___y_3893_ = v___x_3947_;
goto v___jp_3887_;
}
}
else
{
lean_dec(v_a_3939_);
lean_dec(v_binderName_3934_);
lean_dec_ref(v___y_3919_);
lean_dec_ref(v_post_3863_);
lean_dec_ref(v_pre_3861_);
return v___x_3940_;
}
}
else
{
lean_dec(v_binderName_3934_);
lean_dec_ref(v___y_3919_);
lean_dec_ref(v_post_3863_);
lean_dec_ref(v_pre_3861_);
return v___x_3938_;
}
}
case 8:
{
lean_object* v_declName_3948_; lean_object* v_type_3949_; lean_object* v_value_3950_; lean_object* v_body_3951_; uint8_t v_nondep_3952_; lean_object* v___x_3953_; 
v_declName_3948_ = lean_ctor_get(v___y_3919_, 0);
lean_inc(v_declName_3948_);
v_type_3949_ = lean_ctor_get(v___y_3919_, 1);
v_value_3950_ = lean_ctor_get(v___y_3919_, 2);
v_body_3951_ = lean_ctor_get(v___y_3919_, 3);
lean_inc_ref(v_body_3951_);
v_nondep_3952_ = lean_ctor_get_uint8(v___y_3919_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_3949_);
lean_inc_ref(v_post_3863_);
lean_inc_ref(v_pre_3861_);
v___x_3953_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3861_, v_post_3863_, v_type_3949_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_);
if (lean_obj_tag(v___x_3953_) == 0)
{
lean_object* v_a_3954_; lean_object* v___x_3955_; 
v_a_3954_ = lean_ctor_get(v___x_3953_, 0);
lean_inc(v_a_3954_);
lean_dec_ref(v___x_3953_);
lean_inc_ref(v_value_3950_);
lean_inc_ref(v_post_3863_);
lean_inc_ref(v_pre_3861_);
v___x_3955_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3861_, v_post_3863_, v_value_3950_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_);
if (lean_obj_tag(v___x_3955_) == 0)
{
lean_object* v_a_3956_; lean_object* v___x_3957_; 
v_a_3956_ = lean_ctor_get(v___x_3955_, 0);
lean_inc(v_a_3956_);
lean_dec_ref(v___x_3955_);
lean_inc_ref(v_body_3951_);
lean_inc_ref(v_post_3863_);
lean_inc_ref(v_pre_3861_);
v___x_3957_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3861_, v_post_3863_, v_body_3951_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_);
if (lean_obj_tag(v___x_3957_) == 0)
{
lean_object* v_a_3958_; size_t v___x_3959_; size_t v___x_3960_; uint8_t v___x_3961_; 
v_a_3958_ = lean_ctor_get(v___x_3957_, 0);
lean_inc(v_a_3958_);
lean_dec_ref(v___x_3957_);
v___x_3959_ = lean_ptr_addr(v_type_3949_);
v___x_3960_ = lean_ptr_addr(v_a_3954_);
v___x_3961_ = lean_usize_dec_eq(v___x_3959_, v___x_3960_);
if (v___x_3961_ == 0)
{
v___y_3871_ = v_nondep_3952_;
v___y_3872_ = v_a_3954_;
v___y_3873_ = v___y_3919_;
v___y_3874_ = v_declName_3948_;
v___y_3875_ = v_a_3958_;
v___y_3876_ = v_body_3951_;
v___y_3877_ = v_a_3956_;
v___y_3878_ = v___x_3961_;
goto v___jp_3870_;
}
else
{
size_t v___x_3962_; size_t v___x_3963_; uint8_t v___x_3964_; 
v___x_3962_ = lean_ptr_addr(v_value_3950_);
v___x_3963_ = lean_ptr_addr(v_a_3956_);
v___x_3964_ = lean_usize_dec_eq(v___x_3962_, v___x_3963_);
v___y_3871_ = v_nondep_3952_;
v___y_3872_ = v_a_3954_;
v___y_3873_ = v___y_3919_;
v___y_3874_ = v_declName_3948_;
v___y_3875_ = v_a_3958_;
v___y_3876_ = v_body_3951_;
v___y_3877_ = v_a_3956_;
v___y_3878_ = v___x_3964_;
goto v___jp_3870_;
}
}
else
{
lean_dec(v_a_3956_);
lean_dec(v_a_3954_);
lean_dec_ref(v_body_3951_);
lean_dec(v_declName_3948_);
lean_dec_ref(v___y_3919_);
lean_dec_ref(v_post_3863_);
lean_dec_ref(v_pre_3861_);
return v___x_3957_;
}
}
else
{
lean_dec(v_a_3954_);
lean_dec_ref(v_body_3951_);
lean_dec(v_declName_3948_);
lean_dec_ref(v___y_3919_);
lean_dec_ref(v_post_3863_);
lean_dec_ref(v_pre_3861_);
return v___x_3955_;
}
}
else
{
lean_dec_ref(v_body_3951_);
lean_dec(v_declName_3948_);
lean_dec_ref(v___y_3919_);
lean_dec_ref(v_post_3863_);
lean_dec_ref(v_pre_3861_);
return v___x_3953_;
}
}
case 5:
{
lean_object* v_dummy_3965_; lean_object* v_nargs_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; 
v_dummy_3965_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0);
v_nargs_3966_ = l_Lean_Expr_getAppNumArgs(v___y_3919_);
lean_inc(v_nargs_3966_);
v___x_3967_ = lean_mk_array(v_nargs_3966_, v_dummy_3965_);
v___x_3968_ = lean_unsigned_to_nat(1u);
v___x_3969_ = lean_nat_sub(v_nargs_3966_, v___x_3968_);
lean_dec(v_nargs_3966_);
v___x_3970_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9(v_pre_3861_, v_post_3863_, v___y_3919_, v___x_3967_, v___x_3969_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_);
return v___x_3970_;
}
case 10:
{
lean_object* v_data_3971_; lean_object* v_expr_3972_; lean_object* v___x_3973_; 
v_data_3971_ = lean_ctor_get(v___y_3919_, 0);
v_expr_3972_ = lean_ctor_get(v___y_3919_, 1);
lean_inc_ref(v_expr_3972_);
lean_inc_ref(v_post_3863_);
lean_inc_ref(v_pre_3861_);
v___x_3973_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3861_, v_post_3863_, v_expr_3972_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_);
if (lean_obj_tag(v___x_3973_) == 0)
{
lean_object* v_a_3974_; size_t v___x_3975_; size_t v___x_3976_; uint8_t v___x_3977_; 
v_a_3974_ = lean_ctor_get(v___x_3973_, 0);
lean_inc(v_a_3974_);
lean_dec_ref(v___x_3973_);
v___x_3975_ = lean_ptr_addr(v_expr_3972_);
v___x_3976_ = lean_ptr_addr(v_a_3974_);
v___x_3977_ = lean_usize_dec_eq(v___x_3975_, v___x_3976_);
if (v___x_3977_ == 0)
{
lean_object* v___x_3978_; lean_object* v___x_3979_; 
lean_inc(v_data_3971_);
lean_dec_ref(v___y_3919_);
v___x_3978_ = l_Lean_Expr_mdata___override(v_data_3971_, v_a_3974_);
v___x_3979_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__8(v_pre_3861_, v_post_3863_, v___x_3978_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_);
return v___x_3979_;
}
else
{
lean_object* v___x_3980_; 
lean_dec(v_a_3974_);
v___x_3980_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__8(v_pre_3861_, v_post_3863_, v___y_3919_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_);
return v___x_3980_;
}
}
else
{
lean_dec_ref(v___y_3919_);
lean_dec_ref(v_post_3863_);
lean_dec_ref(v_pre_3861_);
return v___x_3973_;
}
}
case 11:
{
lean_object* v_typeName_3981_; lean_object* v_idx_3982_; lean_object* v_struct_3983_; lean_object* v___x_3984_; 
v_typeName_3981_ = lean_ctor_get(v___y_3919_, 0);
v_idx_3982_ = lean_ctor_get(v___y_3919_, 1);
v_struct_3983_ = lean_ctor_get(v___y_3919_, 2);
lean_inc_ref(v_struct_3983_);
lean_inc_ref(v_post_3863_);
lean_inc_ref(v_pre_3861_);
v___x_3984_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3861_, v_post_3863_, v_struct_3983_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_);
if (lean_obj_tag(v___x_3984_) == 0)
{
lean_object* v_a_3985_; size_t v___x_3986_; size_t v___x_3987_; uint8_t v___x_3988_; 
v_a_3985_ = lean_ctor_get(v___x_3984_, 0);
lean_inc(v_a_3985_);
lean_dec_ref(v___x_3984_);
v___x_3986_ = lean_ptr_addr(v_struct_3983_);
v___x_3987_ = lean_ptr_addr(v_a_3985_);
v___x_3988_ = lean_usize_dec_eq(v___x_3986_, v___x_3987_);
if (v___x_3988_ == 0)
{
lean_object* v___x_3989_; lean_object* v___x_3990_; 
lean_inc(v_idx_3982_);
lean_inc(v_typeName_3981_);
lean_dec_ref(v___y_3919_);
v___x_3989_ = l_Lean_Expr_proj___override(v_typeName_3981_, v_idx_3982_, v_a_3985_);
v___x_3990_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__8(v_pre_3861_, v_post_3863_, v___x_3989_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_);
return v___x_3990_;
}
else
{
lean_object* v___x_3991_; 
lean_dec(v_a_3985_);
v___x_3991_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__8(v_pre_3861_, v_post_3863_, v___y_3919_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_);
return v___x_3991_;
}
}
else
{
lean_dec_ref(v___y_3919_);
lean_dec_ref(v_post_3863_);
lean_dec_ref(v_pre_3861_);
return v___x_3984_;
}
}
default: 
{
lean_object* v___x_3992_; 
v___x_3992_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__8(v_pre_3861_, v_post_3863_, v___y_3919_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_);
return v___x_3992_;
}
}
}
}
}
else
{
lean_object* v_a_4004_; lean_object* v___x_4006_; uint8_t v_isShared_4007_; uint8_t v_isSharedCheck_4011_; 
lean_dec_ref(v_post_3863_);
lean_dec_ref(v_e_3862_);
lean_dec_ref(v_pre_3861_);
v_a_4004_ = lean_ctor_get(v___x_3913_, 0);
v_isSharedCheck_4011_ = !lean_is_exclusive(v___x_3913_);
if (v_isSharedCheck_4011_ == 0)
{
v___x_4006_ = v___x_3913_;
v_isShared_4007_ = v_isSharedCheck_4011_;
goto v_resetjp_4005_;
}
else
{
lean_inc(v_a_4004_);
lean_dec(v___x_3913_);
v___x_4006_ = lean_box(0);
v_isShared_4007_ = v_isSharedCheck_4011_;
goto v_resetjp_4005_;
}
v_resetjp_4005_:
{
lean_object* v___x_4009_; 
if (v_isShared_4007_ == 0)
{
v___x_4009_ = v___x_4006_;
goto v_reusejp_4008_;
}
else
{
lean_object* v_reuseFailAlloc_4010_; 
v_reuseFailAlloc_4010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4010_, 0, v_a_4004_);
v___x_4009_ = v_reuseFailAlloc_4010_;
goto v_reusejp_4008_;
}
v_reusejp_4008_:
{
return v___x_4009_;
}
}
}
v___jp_3870_:
{
if (v___y_3878_ == 0)
{
lean_object* v___x_3879_; lean_object* v___x_3880_; 
lean_dec_ref(v___y_3876_);
lean_dec_ref(v___y_3873_);
v___x_3879_ = l_Lean_Expr_letE___override(v___y_3874_, v___y_3872_, v___y_3877_, v___y_3875_, v___y_3871_);
v___x_3880_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__8(v_pre_3861_, v_post_3863_, v___x_3879_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_);
return v___x_3880_;
}
else
{
size_t v___x_3881_; size_t v___x_3882_; uint8_t v___x_3883_; 
v___x_3881_ = lean_ptr_addr(v___y_3876_);
lean_dec_ref(v___y_3876_);
v___x_3882_ = lean_ptr_addr(v___y_3875_);
v___x_3883_ = lean_usize_dec_eq(v___x_3881_, v___x_3882_);
if (v___x_3883_ == 0)
{
lean_object* v___x_3884_; lean_object* v___x_3885_; 
lean_dec_ref(v___y_3873_);
v___x_3884_ = l_Lean_Expr_letE___override(v___y_3874_, v___y_3872_, v___y_3877_, v___y_3875_, v___y_3871_);
v___x_3885_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__8(v_pre_3861_, v_post_3863_, v___x_3884_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_);
return v___x_3885_;
}
else
{
lean_object* v___x_3886_; 
lean_dec_ref(v___y_3877_);
lean_dec_ref(v___y_3875_);
lean_dec(v___y_3874_);
lean_dec_ref(v___y_3872_);
v___x_3886_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__8(v_pre_3861_, v_post_3863_, v___y_3873_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_);
return v___x_3886_;
}
}
}
v___jp_3887_:
{
if (v___y_3893_ == 0)
{
lean_object* v___x_3894_; lean_object* v___x_3895_; 
lean_dec_ref(v___y_3889_);
v___x_3894_ = l_Lean_Expr_lam___override(v___y_3891_, v___y_3888_, v___y_3890_, v___y_3892_);
v___x_3895_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__8(v_pre_3861_, v_post_3863_, v___x_3894_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_);
return v___x_3895_;
}
else
{
uint8_t v___x_3896_; 
v___x_3896_ = l_Lean_instBEqBinderInfo_beq(v___y_3892_, v___y_3892_);
if (v___x_3896_ == 0)
{
lean_object* v___x_3897_; lean_object* v___x_3898_; 
lean_dec_ref(v___y_3889_);
v___x_3897_ = l_Lean_Expr_lam___override(v___y_3891_, v___y_3888_, v___y_3890_, v___y_3892_);
v___x_3898_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__8(v_pre_3861_, v_post_3863_, v___x_3897_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_);
return v___x_3898_;
}
else
{
lean_object* v___x_3899_; 
lean_dec(v___y_3891_);
lean_dec_ref(v___y_3890_);
lean_dec_ref(v___y_3888_);
v___x_3899_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__8(v_pre_3861_, v_post_3863_, v___y_3889_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_);
return v___x_3899_;
}
}
}
v___jp_3900_:
{
if (v___y_3906_ == 0)
{
lean_object* v___x_3907_; lean_object* v___x_3908_; 
lean_dec_ref(v___y_3903_);
v___x_3907_ = l_Lean_Expr_forallE___override(v___y_3902_, v___y_3905_, v___y_3901_, v___y_3904_);
v___x_3908_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__8(v_pre_3861_, v_post_3863_, v___x_3907_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_);
return v___x_3908_;
}
else
{
uint8_t v___x_3909_; 
v___x_3909_ = l_Lean_instBEqBinderInfo_beq(v___y_3904_, v___y_3904_);
if (v___x_3909_ == 0)
{
lean_object* v___x_3910_; lean_object* v___x_3911_; 
lean_dec_ref(v___y_3903_);
v___x_3910_ = l_Lean_Expr_forallE___override(v___y_3902_, v___y_3905_, v___y_3901_, v___y_3904_);
v___x_3911_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__8(v_pre_3861_, v_post_3863_, v___x_3910_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_);
return v___x_3911_;
}
else
{
lean_object* v___x_3912_; 
lean_dec_ref(v___y_3905_);
lean_dec(v___y_3902_);
lean_dec_ref(v___y_3901_);
v___x_3912_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__8(v_pre_3861_, v_post_3863_, v___y_3903_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_);
return v___x_3912_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4___lam__1___boxed(lean_object* v_pre_4012_, lean_object* v_e_4013_, lean_object* v_post_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_){
_start:
{
lean_object* v_res_4021_; 
v_res_4021_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4___lam__1(v_pre_4012_, v_e_4013_, v_post_4014_, v___y_4015_, v___y_4016_, v___y_4017_, v___y_4018_, v___y_4019_);
lean_dec(v___y_4019_);
lean_dec_ref(v___y_4018_);
lean_dec(v___y_4017_);
lean_dec_ref(v___y_4016_);
lean_dec(v___y_4015_);
return v_res_4021_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(lean_object* v_pre_4022_, lean_object* v_post_4023_, lean_object* v_e_4024_, lean_object* v_a_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_){
_start:
{
lean_object* v___x_4031_; lean_object* v___x_4032_; 
lean_inc(v_a_4025_);
v___x_4031_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_4031_, 0, lean_box(0));
lean_closure_set(v___x_4031_, 1, lean_box(0));
lean_closure_set(v___x_4031_, 2, v_a_4025_);
v___x_4032_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__0(lean_box(0), v___x_4031_, v___y_4026_, v___y_4027_, v___y_4028_, v___y_4029_);
if (lean_obj_tag(v___x_4032_) == 0)
{
lean_object* v_a_4033_; lean_object* v___x_4035_; uint8_t v_isShared_4036_; uint8_t v_isSharedCheck_4063_; 
v_a_4033_ = lean_ctor_get(v___x_4032_, 0);
v_isSharedCheck_4063_ = !lean_is_exclusive(v___x_4032_);
if (v_isSharedCheck_4063_ == 0)
{
v___x_4035_ = v___x_4032_;
v_isShared_4036_ = v_isSharedCheck_4063_;
goto v_resetjp_4034_;
}
else
{
lean_inc(v_a_4033_);
lean_dec(v___x_4032_);
v___x_4035_ = lean_box(0);
v_isShared_4036_ = v_isSharedCheck_4063_;
goto v_resetjp_4034_;
}
v_resetjp_4034_:
{
lean_object* v___x_4037_; 
v___x_4037_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___redArg(v_a_4033_, v_e_4024_);
lean_dec(v_a_4033_);
if (lean_obj_tag(v___x_4037_) == 0)
{
lean_object* v___f_4038_; lean_object* v___x_4039_; 
lean_del_object(v___x_4035_);
lean_inc_ref(v_e_4024_);
v___f_4038_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4___lam__1___boxed), 9, 3);
lean_closure_set(v___f_4038_, 0, v_pre_4022_);
lean_closure_set(v___f_4038_, 1, v_e_4024_);
lean_closure_set(v___f_4038_, 2, v_post_4023_);
lean_inc_ref(v___y_4028_);
v___x_4039_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__10___redArg(v___f_4038_, v_a_4025_, v___y_4026_, v___y_4027_, v___y_4028_, v___y_4029_);
if (lean_obj_tag(v___x_4039_) == 0)
{
lean_object* v_a_4040_; lean_object* v___f_4041_; lean_object* v___x_4042_; 
v_a_4040_ = lean_ctor_get(v___x_4039_, 0);
lean_inc(v_a_4040_);
lean_dec_ref(v___x_4039_);
lean_inc(v_a_4040_);
lean_inc(v_a_4025_);
v___f_4041_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__2___boxed), 4, 3);
lean_closure_set(v___f_4041_, 0, v_a_4025_);
lean_closure_set(v___f_4041_, 1, v_e_4024_);
lean_closure_set(v___f_4041_, 2, v_a_4040_);
v___x_4042_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__0(lean_box(0), v___f_4041_, v___y_4026_, v___y_4027_, v___y_4028_, v___y_4029_);
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
lean_dec_ref(v_e_4024_);
return v___x_4039_;
}
}
else
{
lean_object* v_val_4059_; lean_object* v___x_4061_; 
lean_dec_ref(v_e_4024_);
lean_dec_ref(v_post_4023_);
lean_dec_ref(v_pre_4022_);
v_val_4059_ = lean_ctor_get(v___x_4037_, 0);
lean_inc(v_val_4059_);
lean_dec_ref(v___x_4037_);
if (v_isShared_4036_ == 0)
{
lean_ctor_set(v___x_4035_, 0, v_val_4059_);
v___x_4061_ = v___x_4035_;
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
lean_dec_ref(v_e_4024_);
lean_dec_ref(v_post_4023_);
lean_dec_ref(v_pre_4022_);
v_a_4064_ = lean_ctor_get(v___x_4032_, 0);
v_isSharedCheck_4071_ = !lean_is_exclusive(v___x_4032_);
if (v_isSharedCheck_4071_ == 0)
{
v___x_4066_ = v___x_4032_;
v_isShared_4067_ = v_isSharedCheck_4071_;
goto v_resetjp_4065_;
}
else
{
lean_inc(v_a_4064_);
lean_dec(v___x_4032_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__8(lean_object* v_pre_4072_, lean_object* v_post_4073_, lean_object* v_e_4074_, lean_object* v_a_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_){
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
lean_dec_ref(v_a_4082_);
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
lean_dec_ref(v_a_4082_);
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
lean_dec_ref(v_a_4082_);
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
lean_dec_ref(v_e_x3f_4092_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__8___boxed(lean_object* v_pre_4109_, lean_object* v_post_4110_, lean_object* v_e_4111_, lean_object* v_a_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_){
_start:
{
lean_object* v_res_4118_; 
v_res_4118_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__8(v_pre_4109_, v_post_4110_, v_e_4111_, v_a_4112_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_);
lean_dec(v___y_4116_);
lean_dec_ref(v___y_4115_);
lean_dec(v___y_4114_);
lean_dec_ref(v___y_4113_);
lean_dec(v_a_4112_);
return v_res_4118_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7___boxed(lean_object* v_pre_4119_, lean_object* v_post_4120_, lean_object* v_sz_4121_, lean_object* v_i_4122_, lean_object* v_bs_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_){
_start:
{
size_t v_sz_boxed_4130_; size_t v_i_boxed_4131_; lean_object* v_res_4132_; 
v_sz_boxed_4130_ = lean_unbox_usize(v_sz_4121_);
lean_dec(v_sz_4121_);
v_i_boxed_4131_ = lean_unbox_usize(v_i_4122_);
lean_dec(v_i_4122_);
v_res_4132_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_4119_, v_post_4120_, v_sz_boxed_4130_, v_i_boxed_4131_, v_bs_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_);
lean_dec(v___y_4128_);
lean_dec_ref(v___y_4127_);
lean_dec(v___y_4126_);
lean_dec_ref(v___y_4125_);
lean_dec(v___y_4124_);
return v_res_4132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9___boxed(lean_object* v_pre_4133_, lean_object* v_post_4134_, lean_object* v_x_4135_, lean_object* v_x_4136_, lean_object* v_x_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_){
_start:
{
lean_object* v_res_4144_; 
v_res_4144_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9(v_pre_4133_, v_post_4134_, v_x_4135_, v_x_4136_, v_x_4137_, v___y_4138_, v___y_4139_, v___y_4140_, v___y_4141_, v___y_4142_);
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
v___x_4163_ = lean_obj_once(&l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__2, &l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__2_once, _init_l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__2);
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
lean_dec_ref(v___x_4166_);
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
static double _init_l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__6___closed__0(void){
_start:
{
lean_object* v___x_4187_; double v___x_4188_; 
v___x_4187_ = lean_unsigned_to_nat(0u);
v___x_4188_ = lean_float_of_nat(v___x_4187_);
return v___x_4188_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__6(lean_object* v_cls_4192_, lean_object* v_msg_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_){
_start:
{
lean_object* v_ref_4199_; lean_object* v___x_4200_; lean_object* v_a_4201_; lean_object* v___x_4203_; uint8_t v_isShared_4204_; uint8_t v_isSharedCheck_4245_; 
v_ref_4199_ = lean_ctor_get(v___y_4196_, 5);
v___x_4200_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15_spec__16(v_msg_4193_, v___y_4194_, v___y_4195_, v___y_4196_, v___y_4197_);
v_a_4201_ = lean_ctor_get(v___x_4200_, 0);
v_isSharedCheck_4245_ = !lean_is_exclusive(v___x_4200_);
if (v_isSharedCheck_4245_ == 0)
{
v___x_4203_ = v___x_4200_;
v_isShared_4204_ = v_isSharedCheck_4245_;
goto v_resetjp_4202_;
}
else
{
lean_inc(v_a_4201_);
lean_dec(v___x_4200_);
v___x_4203_ = lean_box(0);
v_isShared_4204_ = v_isSharedCheck_4245_;
goto v_resetjp_4202_;
}
v_resetjp_4202_:
{
lean_object* v___x_4205_; lean_object* v_traceState_4206_; lean_object* v_env_4207_; lean_object* v_nextMacroScope_4208_; lean_object* v_ngen_4209_; lean_object* v_auxDeclNGen_4210_; lean_object* v_cache_4211_; lean_object* v_messages_4212_; lean_object* v_infoState_4213_; lean_object* v_snapshotTasks_4214_; lean_object* v___x_4216_; uint8_t v_isShared_4217_; uint8_t v_isSharedCheck_4244_; 
v___x_4205_ = lean_st_ref_take(v___y_4197_);
v_traceState_4206_ = lean_ctor_get(v___x_4205_, 4);
v_env_4207_ = lean_ctor_get(v___x_4205_, 0);
v_nextMacroScope_4208_ = lean_ctor_get(v___x_4205_, 1);
v_ngen_4209_ = lean_ctor_get(v___x_4205_, 2);
v_auxDeclNGen_4210_ = lean_ctor_get(v___x_4205_, 3);
v_cache_4211_ = lean_ctor_get(v___x_4205_, 5);
v_messages_4212_ = lean_ctor_get(v___x_4205_, 6);
v_infoState_4213_ = lean_ctor_get(v___x_4205_, 7);
v_snapshotTasks_4214_ = lean_ctor_get(v___x_4205_, 8);
v_isSharedCheck_4244_ = !lean_is_exclusive(v___x_4205_);
if (v_isSharedCheck_4244_ == 0)
{
v___x_4216_ = v___x_4205_;
v_isShared_4217_ = v_isSharedCheck_4244_;
goto v_resetjp_4215_;
}
else
{
lean_inc(v_snapshotTasks_4214_);
lean_inc(v_infoState_4213_);
lean_inc(v_messages_4212_);
lean_inc(v_cache_4211_);
lean_inc(v_traceState_4206_);
lean_inc(v_auxDeclNGen_4210_);
lean_inc(v_ngen_4209_);
lean_inc(v_nextMacroScope_4208_);
lean_inc(v_env_4207_);
lean_dec(v___x_4205_);
v___x_4216_ = lean_box(0);
v_isShared_4217_ = v_isSharedCheck_4244_;
goto v_resetjp_4215_;
}
v_resetjp_4215_:
{
uint64_t v_tid_4218_; lean_object* v_traces_4219_; lean_object* v___x_4221_; uint8_t v_isShared_4222_; uint8_t v_isSharedCheck_4243_; 
v_tid_4218_ = lean_ctor_get_uint64(v_traceState_4206_, sizeof(void*)*1);
v_traces_4219_ = lean_ctor_get(v_traceState_4206_, 0);
v_isSharedCheck_4243_ = !lean_is_exclusive(v_traceState_4206_);
if (v_isSharedCheck_4243_ == 0)
{
v___x_4221_ = v_traceState_4206_;
v_isShared_4222_ = v_isSharedCheck_4243_;
goto v_resetjp_4220_;
}
else
{
lean_inc(v_traces_4219_);
lean_dec(v_traceState_4206_);
v___x_4221_ = lean_box(0);
v_isShared_4222_ = v_isSharedCheck_4243_;
goto v_resetjp_4220_;
}
v_resetjp_4220_:
{
lean_object* v___x_4223_; double v___x_4224_; uint8_t v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4233_; 
v___x_4223_ = lean_box(0);
v___x_4224_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__6___closed__0, &l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__6___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__6___closed__0);
v___x_4225_ = 0;
v___x_4226_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__6___closed__1));
v___x_4227_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4227_, 0, v_cls_4192_);
lean_ctor_set(v___x_4227_, 1, v___x_4223_);
lean_ctor_set(v___x_4227_, 2, v___x_4226_);
lean_ctor_set_float(v___x_4227_, sizeof(void*)*3, v___x_4224_);
lean_ctor_set_float(v___x_4227_, sizeof(void*)*3 + 8, v___x_4224_);
lean_ctor_set_uint8(v___x_4227_, sizeof(void*)*3 + 16, v___x_4225_);
v___x_4228_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__6___closed__2));
v___x_4229_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4229_, 0, v___x_4227_);
lean_ctor_set(v___x_4229_, 1, v_a_4201_);
lean_ctor_set(v___x_4229_, 2, v___x_4228_);
lean_inc(v_ref_4199_);
v___x_4230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4230_, 0, v_ref_4199_);
lean_ctor_set(v___x_4230_, 1, v___x_4229_);
v___x_4231_ = l_Lean_PersistentArray_push___redArg(v_traces_4219_, v___x_4230_);
if (v_isShared_4222_ == 0)
{
lean_ctor_set(v___x_4221_, 0, v___x_4231_);
v___x_4233_ = v___x_4221_;
goto v_reusejp_4232_;
}
else
{
lean_object* v_reuseFailAlloc_4242_; 
v_reuseFailAlloc_4242_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4242_, 0, v___x_4231_);
lean_ctor_set_uint64(v_reuseFailAlloc_4242_, sizeof(void*)*1, v_tid_4218_);
v___x_4233_ = v_reuseFailAlloc_4242_;
goto v_reusejp_4232_;
}
v_reusejp_4232_:
{
lean_object* v___x_4235_; 
if (v_isShared_4217_ == 0)
{
lean_ctor_set(v___x_4216_, 4, v___x_4233_);
v___x_4235_ = v___x_4216_;
goto v_reusejp_4234_;
}
else
{
lean_object* v_reuseFailAlloc_4241_; 
v_reuseFailAlloc_4241_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4241_, 0, v_env_4207_);
lean_ctor_set(v_reuseFailAlloc_4241_, 1, v_nextMacroScope_4208_);
lean_ctor_set(v_reuseFailAlloc_4241_, 2, v_ngen_4209_);
lean_ctor_set(v_reuseFailAlloc_4241_, 3, v_auxDeclNGen_4210_);
lean_ctor_set(v_reuseFailAlloc_4241_, 4, v___x_4233_);
lean_ctor_set(v_reuseFailAlloc_4241_, 5, v_cache_4211_);
lean_ctor_set(v_reuseFailAlloc_4241_, 6, v_messages_4212_);
lean_ctor_set(v_reuseFailAlloc_4241_, 7, v_infoState_4213_);
lean_ctor_set(v_reuseFailAlloc_4241_, 8, v_snapshotTasks_4214_);
v___x_4235_ = v_reuseFailAlloc_4241_;
goto v_reusejp_4234_;
}
v_reusejp_4234_:
{
lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4239_; 
v___x_4236_ = lean_st_ref_set(v___y_4197_, v___x_4235_);
v___x_4237_ = lean_box(0);
if (v_isShared_4204_ == 0)
{
lean_ctor_set(v___x_4203_, 0, v___x_4237_);
v___x_4239_ = v___x_4203_;
goto v_reusejp_4238_;
}
else
{
lean_object* v_reuseFailAlloc_4240_; 
v_reuseFailAlloc_4240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4240_, 0, v___x_4237_);
v___x_4239_ = v_reuseFailAlloc_4240_;
goto v_reusejp_4238_;
}
v_reusejp_4238_:
{
return v___x_4239_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__6___boxed(lean_object* v_cls_4246_, lean_object* v_msg_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_, lean_object* v___y_4252_){
_start:
{
lean_object* v_res_4253_; 
v_res_4253_ = l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__6(v_cls_4246_, v_msg_4247_, v___y_4248_, v___y_4249_, v___y_4250_, v___y_4251_);
lean_dec(v___y_4251_);
lean_dec_ref(v___y_4250_);
lean_dec(v___y_4249_);
lean_dec_ref(v___y_4248_);
return v_res_4253_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_preprocess_spec__2(size_t v_sz_4254_, size_t v_i_4255_, lean_object* v_bs_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_){
_start:
{
uint8_t v___x_4262_; 
v___x_4262_ = lean_usize_dec_lt(v_i_4255_, v_sz_4254_);
if (v___x_4262_ == 0)
{
lean_object* v___x_4263_; 
v___x_4263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4263_, 0, v_bs_4256_);
return v___x_4263_;
}
else
{
lean_object* v_v_4264_; lean_object* v___x_4265_; 
v_v_4264_ = lean_array_uget_borrowed(v_bs_4256_, v_i_4255_);
lean_inc(v_v_4264_);
v___x_4265_ = l_Lean_Elab_WF_mkWfParam(v_v_4264_, v___y_4257_, v___y_4258_, v___y_4259_, v___y_4260_);
if (lean_obj_tag(v___x_4265_) == 0)
{
lean_object* v_a_4266_; lean_object* v___x_4267_; lean_object* v_bs_x27_4268_; size_t v___x_4269_; size_t v___x_4270_; lean_object* v___x_4271_; 
v_a_4266_ = lean_ctor_get(v___x_4265_, 0);
lean_inc(v_a_4266_);
lean_dec_ref(v___x_4265_);
v___x_4267_ = lean_unsigned_to_nat(0u);
v_bs_x27_4268_ = lean_array_uset(v_bs_4256_, v_i_4255_, v___x_4267_);
v___x_4269_ = ((size_t)1ULL);
v___x_4270_ = lean_usize_add(v_i_4255_, v___x_4269_);
v___x_4271_ = lean_array_uset(v_bs_x27_4268_, v_i_4255_, v_a_4266_);
v_i_4255_ = v___x_4270_;
v_bs_4256_ = v___x_4271_;
goto _start;
}
else
{
lean_object* v_a_4273_; lean_object* v___x_4275_; uint8_t v_isShared_4276_; uint8_t v_isSharedCheck_4280_; 
lean_dec_ref(v_bs_4256_);
v_a_4273_ = lean_ctor_get(v___x_4265_, 0);
v_isSharedCheck_4280_ = !lean_is_exclusive(v___x_4265_);
if (v_isSharedCheck_4280_ == 0)
{
v___x_4275_ = v___x_4265_;
v_isShared_4276_ = v_isSharedCheck_4280_;
goto v_resetjp_4274_;
}
else
{
lean_inc(v_a_4273_);
lean_dec(v___x_4265_);
v___x_4275_ = lean_box(0);
v_isShared_4276_ = v_isSharedCheck_4280_;
goto v_resetjp_4274_;
}
v_resetjp_4274_:
{
lean_object* v___x_4278_; 
if (v_isShared_4276_ == 0)
{
v___x_4278_ = v___x_4275_;
goto v_reusejp_4277_;
}
else
{
lean_object* v_reuseFailAlloc_4279_; 
v_reuseFailAlloc_4279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4279_, 0, v_a_4273_);
v___x_4278_ = v_reuseFailAlloc_4279_;
goto v_reusejp_4277_;
}
v_reusejp_4277_:
{
return v___x_4278_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_preprocess_spec__2___boxed(lean_object* v_sz_4281_, lean_object* v_i_4282_, lean_object* v_bs_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_){
_start:
{
size_t v_sz_boxed_4289_; size_t v_i_boxed_4290_; lean_object* v_res_4291_; 
v_sz_boxed_4289_ = lean_unbox_usize(v_sz_4281_);
lean_dec(v_sz_4281_);
v_i_boxed_4290_ = lean_unbox_usize(v_i_4282_);
lean_dec(v_i_4282_);
v_res_4291_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_preprocess_spec__2(v_sz_boxed_4289_, v_i_boxed_4290_, v_bs_4283_, v___y_4284_, v___y_4285_, v___y_4286_, v___y_4287_);
lean_dec(v___y_4287_);
lean_dec_ref(v___y_4286_);
lean_dec(v___y_4285_);
lean_dec_ref(v___y_4284_);
return v_res_4291_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__0___closed__0(void){
_start:
{
lean_object* v___x_4292_; 
v___x_4292_ = l_Lean_Meta_DiscrTree_empty(lean_box(0));
return v___x_4292_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4293_; 
v___x_4293_ = l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3(lean_box(0));
return v___x_4293_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; 
v___x_4294_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__0___closed__1, &l_Lean_Elab_WF_preprocess___lam__0___closed__1_once, _init_l_Lean_Elab_WF_preprocess___lam__0___closed__1);
v___x_4295_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__0___closed__0, &l_Lean_Elab_WF_preprocess___lam__0___closed__0_once, _init_l_Lean_Elab_WF_preprocess___lam__0___closed__0);
v___x_4296_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4296_, 0, v___x_4295_);
lean_ctor_set(v___x_4296_, 1, v___x_4295_);
lean_ctor_set(v___x_4296_, 2, v___x_4294_);
lean_ctor_set(v___x_4296_, 3, v___x_4294_);
return v___x_4296_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4297_; 
v___x_4297_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4297_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__0___closed__4(void){
_start:
{
lean_object* v___x_4298_; lean_object* v___x_4299_; 
v___x_4298_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__0___closed__3, &l_Lean_Elab_WF_preprocess___lam__0___closed__3_once, _init_l_Lean_Elab_WF_preprocess___lam__0___closed__3);
v___x_4299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4299_, 0, v___x_4298_);
return v___x_4299_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; 
v___x_4300_ = lean_unsigned_to_nat(0u);
v___x_4301_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__0___closed__4, &l_Lean_Elab_WF_preprocess___lam__0___closed__4_once, _init_l_Lean_Elab_WF_preprocess___lam__0___closed__4);
v___x_4302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4302_, 0, v___x_4301_);
lean_ctor_set(v___x_4302_, 1, v___x_4300_);
return v___x_4302_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__0___closed__6(void){
_start:
{
lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; 
v___x_4303_ = lean_unsigned_to_nat(32u);
v___x_4304_ = lean_mk_empty_array_with_capacity(v___x_4303_);
v___x_4305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4305_, 0, v___x_4304_);
return v___x_4305_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__0___closed__7(void){
_start:
{
size_t v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; 
v___x_4306_ = ((size_t)5ULL);
v___x_4307_ = lean_unsigned_to_nat(0u);
v___x_4308_ = lean_unsigned_to_nat(32u);
v___x_4309_ = lean_mk_empty_array_with_capacity(v___x_4308_);
v___x_4310_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__0___closed__6, &l_Lean_Elab_WF_preprocess___lam__0___closed__6_once, _init_l_Lean_Elab_WF_preprocess___lam__0___closed__6);
v___x_4311_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4311_, 0, v___x_4310_);
lean_ctor_set(v___x_4311_, 1, v___x_4309_);
lean_ctor_set(v___x_4311_, 2, v___x_4307_);
lean_ctor_set(v___x_4311_, 3, v___x_4307_);
lean_ctor_set_usize(v___x_4311_, 4, v___x_4306_);
return v___x_4311_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__0___closed__8(void){
_start:
{
lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; 
v___x_4312_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__0___closed__7, &l_Lean_Elab_WF_preprocess___lam__0___closed__7_once, _init_l_Lean_Elab_WF_preprocess___lam__0___closed__7);
v___x_4313_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__0___closed__4, &l_Lean_Elab_WF_preprocess___lam__0___closed__4_once, _init_l_Lean_Elab_WF_preprocess___lam__0___closed__4);
v___x_4314_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4314_, 0, v___x_4313_);
lean_ctor_set(v___x_4314_, 1, v___x_4313_);
lean_ctor_set(v___x_4314_, 2, v___x_4313_);
lean_ctor_set(v___x_4314_, 3, v___x_4312_);
return v___x_4314_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__0___closed__9(void){
_start:
{
lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; 
v___x_4315_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__0___closed__8, &l_Lean_Elab_WF_preprocess___lam__0___closed__8_once, _init_l_Lean_Elab_WF_preprocess___lam__0___closed__8);
v___x_4316_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__0___closed__5, &l_Lean_Elab_WF_preprocess___lam__0___closed__5_once, _init_l_Lean_Elab_WF_preprocess___lam__0___closed__5);
v___x_4317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4317_, 0, v___x_4316_);
lean_ctor_set(v___x_4317_, 1, v___x_4315_);
return v___x_4317_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__0___closed__13(void){
_start:
{
lean_object* v___x_4324_; lean_object* v___x_4325_; 
v___x_4324_ = ((lean_object*)(l_Lean_Elab_WF_preprocess___lam__0___closed__12));
v___x_4325_ = l_Lean_stringToMessageData(v___x_4324_);
return v___x_4325_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__0___closed__15(void){
_start:
{
lean_object* v___x_4327_; lean_object* v___x_4328_; 
v___x_4327_ = ((lean_object*)(l_Lean_Elab_WF_preprocess___lam__0___closed__14));
v___x_4328_ = l_Lean_stringToMessageData(v___x_4327_);
return v___x_4328_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__0___closed__17(void){
_start:
{
lean_object* v___x_4330_; lean_object* v___x_4331_; 
v___x_4330_ = ((lean_object*)(l_Lean_Elab_WF_preprocess___lam__0___closed__16));
v___x_4331_ = l_Lean_stringToMessageData(v___x_4330_);
return v___x_4331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preprocess___lam__0(uint8_t v___x_4332_, lean_object* v_a_4333_, lean_object* v___f_4334_, lean_object* v___f_4335_, lean_object* v_xs_4336_, lean_object* v_x_4337_, lean_object* v___y_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_, lean_object* v___y_4341_){
_start:
{
size_t v_sz_4343_; size_t v___x_4344_; lean_object* v___x_4345_; 
v_sz_4343_ = lean_array_size(v_xs_4336_);
v___x_4344_ = ((size_t)0ULL);
lean_inc_ref(v_xs_4336_);
v___x_4345_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_preprocess_spec__2(v_sz_4343_, v___x_4344_, v_xs_4336_, v___y_4338_, v___y_4339_, v___y_4340_, v___y_4341_);
if (lean_obj_tag(v___x_4345_) == 0)
{
lean_object* v_a_4346_; lean_object* v___x_4347_; lean_object* v___x_4348_; lean_object* v___x_4349_; 
v_a_4346_ = lean_ctor_get(v___x_4345_, 0);
lean_inc(v_a_4346_);
lean_dec_ref(v___x_4345_);
v___x_4347_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__0___closed__2, &l_Lean_Elab_WF_preprocess___lam__0___closed__2_once, _init_l_Lean_Elab_WF_preprocess___lam__0___closed__2);
v___x_4348_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__26___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_12_));
v___x_4349_ = l_Lean_Meta_Simp_Simprocs_add(v___x_4347_, v___x_4348_, v___x_4332_, v___y_4340_, v___y_4341_);
if (lean_obj_tag(v___x_4349_) == 0)
{
lean_object* v_a_4350_; lean_object* v___x_4351_; uint8_t v___x_4352_; lean_object* v___x_4353_; 
v_a_4350_ = lean_ctor_get(v___x_4349_, 0);
lean_inc(v_a_4350_);
lean_dec_ref(v___x_4349_);
v___x_4351_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__31___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_12_));
v___x_4352_ = 0;
v___x_4353_ = l_Lean_Meta_Simp_Simprocs_add(v_a_4350_, v___x_4351_, v___x_4352_, v___y_4340_, v___y_4341_);
if (lean_obj_tag(v___x_4353_) == 0)
{
lean_object* v_a_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; 
v_a_4354_ = lean_ctor_get(v___x_4353_, 0);
lean_inc(v_a_4354_);
lean_dec_ref(v___x_4353_);
v___x_4355_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__60___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12_));
v___x_4356_ = l_Lean_Meta_Simp_Simprocs_add(v_a_4354_, v___x_4355_, v___x_4332_, v___y_4340_, v___y_4341_);
if (lean_obj_tag(v___x_4356_) == 0)
{
lean_object* v_a_4357_; lean_object* v___x_4358_; 
v_a_4357_ = lean_ctor_get(v___x_4356_, 0);
lean_inc(v_a_4357_);
lean_dec_ref(v___x_4356_);
v___x_4358_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg(v___y_4338_, v___y_4340_, v___y_4341_);
if (lean_obj_tag(v___x_4358_) == 0)
{
lean_object* v_a_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; 
v_a_4359_ = lean_ctor_get(v___x_4358_, 0);
lean_inc(v_a_4359_);
lean_dec_ref(v___x_4358_);
v___x_4360_ = l_Lean_Expr_beta(v_a_4333_, v_a_4346_);
v___x_4361_ = lean_unsigned_to_nat(1u);
v___x_4362_ = lean_mk_empty_array_with_capacity(v___x_4361_);
v___x_4363_ = lean_array_push(v___x_4362_, v_a_4357_);
v___x_4364_ = lean_box(0);
v___x_4365_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__0___closed__9, &l_Lean_Elab_WF_preprocess___lam__0___closed__9_once, _init_l_Lean_Elab_WF_preprocess___lam__0___closed__9);
lean_inc_ref(v___x_4360_);
v___x_4366_ = l_Lean_Meta_simp(v___x_4360_, v_a_4359_, v___x_4363_, v___x_4364_, v___x_4365_, v___y_4338_, v___y_4339_, v___y_4340_, v___y_4341_);
if (lean_obj_tag(v___x_4366_) == 0)
{
lean_object* v_a_4367_; lean_object* v_fst_4368_; lean_object* v___x_4370_; uint8_t v_isShared_4371_; uint8_t v_isSharedCheck_4434_; 
v_a_4367_ = lean_ctor_get(v___x_4366_, 0);
lean_inc(v_a_4367_);
lean_dec_ref(v___x_4366_);
v_fst_4368_ = lean_ctor_get(v_a_4367_, 0);
v_isSharedCheck_4434_ = !lean_is_exclusive(v_a_4367_);
if (v_isSharedCheck_4434_ == 0)
{
lean_object* v_unused_4435_; 
v_unused_4435_ = lean_ctor_get(v_a_4367_, 1);
lean_dec(v_unused_4435_);
v___x_4370_ = v_a_4367_;
v_isShared_4371_ = v_isSharedCheck_4434_;
goto v_resetjp_4369_;
}
else
{
lean_inc(v_fst_4368_);
lean_dec(v_a_4367_);
v___x_4370_ = lean_box(0);
v_isShared_4371_ = v_isSharedCheck_4434_;
goto v_resetjp_4369_;
}
v_resetjp_4369_:
{
lean_object* v_expr_4372_; lean_object* v_proof_x3f_4373_; uint8_t v_cache_4374_; lean_object* v___x_4376_; uint8_t v_isShared_4377_; uint8_t v_isSharedCheck_4433_; 
v_expr_4372_ = lean_ctor_get(v_fst_4368_, 0);
v_proof_x3f_4373_ = lean_ctor_get(v_fst_4368_, 1);
v_cache_4374_ = lean_ctor_get_uint8(v_fst_4368_, sizeof(void*)*2);
v_isSharedCheck_4433_ = !lean_is_exclusive(v_fst_4368_);
if (v_isSharedCheck_4433_ == 0)
{
v___x_4376_ = v_fst_4368_;
v_isShared_4377_ = v_isSharedCheck_4433_;
goto v_resetjp_4375_;
}
else
{
lean_inc(v_proof_x3f_4373_);
lean_inc(v_expr_4372_);
lean_dec(v_fst_4368_);
v___x_4376_ = lean_box(0);
v_isShared_4377_ = v_isSharedCheck_4433_;
goto v_resetjp_4375_;
}
v_resetjp_4375_:
{
lean_object* v___x_4378_; 
lean_inc_ref(v_expr_4372_);
v___x_4378_ = l_Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4(v_expr_4372_, v___f_4334_, v___f_4335_, v___y_4338_, v___y_4339_, v___y_4340_, v___y_4341_);
if (lean_obj_tag(v___x_4378_) == 0)
{
lean_object* v_a_4379_; lean_object* v___x_4380_; 
v_a_4379_ = lean_ctor_get(v___x_4378_, 0);
lean_inc(v_a_4379_);
lean_dec_ref(v___x_4378_);
v___x_4380_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet(v_a_4379_, v___y_4338_, v___y_4339_, v___y_4340_, v___y_4341_);
if (lean_obj_tag(v___x_4380_) == 0)
{
lean_object* v_a_4381_; lean_object* v___y_4383_; lean_object* v___y_4384_; lean_object* v___y_4385_; lean_object* v___y_4386_; lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v_a_4393_; uint8_t v___x_4394_; 
v_a_4381_ = lean_ctor_get(v___x_4380_, 0);
lean_inc(v_a_4381_);
lean_dec_ref(v___x_4380_);
v___x_4391_ = ((lean_object*)(l_Lean_Elab_WF_preprocess___lam__0___closed__11));
v___x_4392_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_WF_preprocess_spec__5___redArg(v___x_4391_, v___y_4340_);
v_a_4393_ = lean_ctor_get(v___x_4392_, 0);
lean_inc(v_a_4393_);
lean_dec_ref(v___x_4392_);
v___x_4394_ = lean_unbox(v_a_4393_);
lean_dec(v_a_4393_);
if (v___x_4394_ == 0)
{
lean_dec_ref(v_expr_4372_);
lean_del_object(v___x_4370_);
lean_dec_ref(v___x_4360_);
v___y_4383_ = v___y_4338_;
v___y_4384_ = v___y_4339_;
v___y_4385_ = v___y_4340_;
v___y_4386_ = v___y_4341_;
goto v___jp_4382_;
}
else
{
lean_object* v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4398_; 
v___x_4395_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__0___closed__13, &l_Lean_Elab_WF_preprocess___lam__0___closed__13_once, _init_l_Lean_Elab_WF_preprocess___lam__0___closed__13);
v___x_4396_ = l_Lean_indentExpr(v___x_4360_);
if (v_isShared_4371_ == 0)
{
lean_ctor_set_tag(v___x_4370_, 7);
lean_ctor_set(v___x_4370_, 1, v___x_4396_);
lean_ctor_set(v___x_4370_, 0, v___x_4395_);
v___x_4398_ = v___x_4370_;
goto v_reusejp_4397_;
}
else
{
lean_object* v_reuseFailAlloc_4416_; 
v_reuseFailAlloc_4416_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4416_, 0, v___x_4395_);
lean_ctor_set(v_reuseFailAlloc_4416_, 1, v___x_4396_);
v___x_4398_ = v_reuseFailAlloc_4416_;
goto v_reusejp_4397_;
}
v_reusejp_4397_:
{
lean_object* v___x_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; lean_object* v___x_4402_; lean_object* v___x_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; 
v___x_4399_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__0___closed__15, &l_Lean_Elab_WF_preprocess___lam__0___closed__15_once, _init_l_Lean_Elab_WF_preprocess___lam__0___closed__15);
v___x_4400_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4400_, 0, v___x_4398_);
lean_ctor_set(v___x_4400_, 1, v___x_4399_);
v___x_4401_ = l_Lean_indentExpr(v_expr_4372_);
v___x_4402_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4402_, 0, v___x_4400_);
lean_ctor_set(v___x_4402_, 1, v___x_4401_);
v___x_4403_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__0___closed__17, &l_Lean_Elab_WF_preprocess___lam__0___closed__17_once, _init_l_Lean_Elab_WF_preprocess___lam__0___closed__17);
v___x_4404_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4404_, 0, v___x_4402_);
lean_ctor_set(v___x_4404_, 1, v___x_4403_);
lean_inc(v_a_4381_);
v___x_4405_ = l_Lean_indentExpr(v_a_4381_);
v___x_4406_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4406_, 0, v___x_4404_);
lean_ctor_set(v___x_4406_, 1, v___x_4405_);
v___x_4407_ = l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__6(v___x_4391_, v___x_4406_, v___y_4338_, v___y_4339_, v___y_4340_, v___y_4341_);
if (lean_obj_tag(v___x_4407_) == 0)
{
lean_dec_ref(v___x_4407_);
v___y_4383_ = v___y_4338_;
v___y_4384_ = v___y_4339_;
v___y_4385_ = v___y_4340_;
v___y_4386_ = v___y_4341_;
goto v___jp_4382_;
}
else
{
lean_object* v_a_4408_; lean_object* v___x_4410_; uint8_t v_isShared_4411_; uint8_t v_isSharedCheck_4415_; 
lean_dec(v_a_4381_);
lean_del_object(v___x_4376_);
lean_dec(v_proof_x3f_4373_);
lean_dec_ref(v_xs_4336_);
v_a_4408_ = lean_ctor_get(v___x_4407_, 0);
v_isSharedCheck_4415_ = !lean_is_exclusive(v___x_4407_);
if (v_isSharedCheck_4415_ == 0)
{
v___x_4410_ = v___x_4407_;
v_isShared_4411_ = v_isSharedCheck_4415_;
goto v_resetjp_4409_;
}
else
{
lean_inc(v_a_4408_);
lean_dec(v___x_4407_);
v___x_4410_ = lean_box(0);
v_isShared_4411_ = v_isSharedCheck_4415_;
goto v_resetjp_4409_;
}
v_resetjp_4409_:
{
lean_object* v___x_4413_; 
if (v_isShared_4411_ == 0)
{
v___x_4413_ = v___x_4410_;
goto v_reusejp_4412_;
}
else
{
lean_object* v_reuseFailAlloc_4414_; 
v_reuseFailAlloc_4414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4414_, 0, v_a_4408_);
v___x_4413_ = v_reuseFailAlloc_4414_;
goto v_reusejp_4412_;
}
v_reusejp_4412_:
{
return v___x_4413_;
}
}
}
}
}
v___jp_4382_:
{
lean_object* v___x_4388_; 
if (v_isShared_4377_ == 0)
{
lean_ctor_set(v___x_4376_, 0, v_a_4381_);
v___x_4388_ = v___x_4376_;
goto v_reusejp_4387_;
}
else
{
lean_object* v_reuseFailAlloc_4390_; 
v_reuseFailAlloc_4390_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_4390_, 0, v_a_4381_);
lean_ctor_set(v_reuseFailAlloc_4390_, 1, v_proof_x3f_4373_);
lean_ctor_set_uint8(v_reuseFailAlloc_4390_, sizeof(void*)*2, v_cache_4374_);
v___x_4388_ = v_reuseFailAlloc_4390_;
goto v_reusejp_4387_;
}
v_reusejp_4387_:
{
lean_object* v___x_4389_; 
v___x_4389_ = l_Lean_Meta_Simp_Result_addLambdas(v___x_4388_, v_xs_4336_, v___y_4383_, v___y_4384_, v___y_4385_, v___y_4386_);
lean_dec_ref(v_xs_4336_);
return v___x_4389_;
}
}
}
else
{
lean_object* v_a_4417_; lean_object* v___x_4419_; uint8_t v_isShared_4420_; uint8_t v_isSharedCheck_4424_; 
lean_del_object(v___x_4376_);
lean_dec(v_proof_x3f_4373_);
lean_dec_ref(v_expr_4372_);
lean_del_object(v___x_4370_);
lean_dec_ref(v___x_4360_);
lean_dec_ref(v_xs_4336_);
v_a_4417_ = lean_ctor_get(v___x_4380_, 0);
v_isSharedCheck_4424_ = !lean_is_exclusive(v___x_4380_);
if (v_isSharedCheck_4424_ == 0)
{
v___x_4419_ = v___x_4380_;
v_isShared_4420_ = v_isSharedCheck_4424_;
goto v_resetjp_4418_;
}
else
{
lean_inc(v_a_4417_);
lean_dec(v___x_4380_);
v___x_4419_ = lean_box(0);
v_isShared_4420_ = v_isSharedCheck_4424_;
goto v_resetjp_4418_;
}
v_resetjp_4418_:
{
lean_object* v___x_4422_; 
if (v_isShared_4420_ == 0)
{
v___x_4422_ = v___x_4419_;
goto v_reusejp_4421_;
}
else
{
lean_object* v_reuseFailAlloc_4423_; 
v_reuseFailAlloc_4423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4423_, 0, v_a_4417_);
v___x_4422_ = v_reuseFailAlloc_4423_;
goto v_reusejp_4421_;
}
v_reusejp_4421_:
{
return v___x_4422_;
}
}
}
}
else
{
lean_object* v_a_4425_; lean_object* v___x_4427_; uint8_t v_isShared_4428_; uint8_t v_isSharedCheck_4432_; 
lean_del_object(v___x_4376_);
lean_dec(v_proof_x3f_4373_);
lean_dec_ref(v_expr_4372_);
lean_del_object(v___x_4370_);
lean_dec_ref(v___x_4360_);
lean_dec_ref(v_xs_4336_);
v_a_4425_ = lean_ctor_get(v___x_4378_, 0);
v_isSharedCheck_4432_ = !lean_is_exclusive(v___x_4378_);
if (v_isSharedCheck_4432_ == 0)
{
v___x_4427_ = v___x_4378_;
v_isShared_4428_ = v_isSharedCheck_4432_;
goto v_resetjp_4426_;
}
else
{
lean_inc(v_a_4425_);
lean_dec(v___x_4378_);
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
}
}
else
{
lean_object* v_a_4436_; lean_object* v___x_4438_; uint8_t v_isShared_4439_; uint8_t v_isSharedCheck_4443_; 
lean_dec_ref(v___x_4360_);
lean_dec_ref(v_xs_4336_);
lean_dec_ref(v___f_4335_);
lean_dec_ref(v___f_4334_);
v_a_4436_ = lean_ctor_get(v___x_4366_, 0);
v_isSharedCheck_4443_ = !lean_is_exclusive(v___x_4366_);
if (v_isSharedCheck_4443_ == 0)
{
v___x_4438_ = v___x_4366_;
v_isShared_4439_ = v_isSharedCheck_4443_;
goto v_resetjp_4437_;
}
else
{
lean_inc(v_a_4436_);
lean_dec(v___x_4366_);
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
lean_dec(v_a_4357_);
lean_dec(v_a_4346_);
lean_dec_ref(v_xs_4336_);
lean_dec_ref(v___f_4335_);
lean_dec_ref(v___f_4334_);
lean_dec_ref(v_a_4333_);
v_a_4444_ = lean_ctor_get(v___x_4358_, 0);
v_isSharedCheck_4451_ = !lean_is_exclusive(v___x_4358_);
if (v_isSharedCheck_4451_ == 0)
{
v___x_4446_ = v___x_4358_;
v_isShared_4447_ = v_isSharedCheck_4451_;
goto v_resetjp_4445_;
}
else
{
lean_inc(v_a_4444_);
lean_dec(v___x_4358_);
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
lean_dec(v_a_4346_);
lean_dec_ref(v_xs_4336_);
lean_dec_ref(v___f_4335_);
lean_dec_ref(v___f_4334_);
lean_dec_ref(v_a_4333_);
v_a_4452_ = lean_ctor_get(v___x_4356_, 0);
v_isSharedCheck_4459_ = !lean_is_exclusive(v___x_4356_);
if (v_isSharedCheck_4459_ == 0)
{
v___x_4454_ = v___x_4356_;
v_isShared_4455_ = v_isSharedCheck_4459_;
goto v_resetjp_4453_;
}
else
{
lean_inc(v_a_4452_);
lean_dec(v___x_4356_);
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
lean_dec(v_a_4346_);
lean_dec_ref(v_xs_4336_);
lean_dec_ref(v___f_4335_);
lean_dec_ref(v___f_4334_);
lean_dec_ref(v_a_4333_);
v_a_4460_ = lean_ctor_get(v___x_4353_, 0);
v_isSharedCheck_4467_ = !lean_is_exclusive(v___x_4353_);
if (v_isSharedCheck_4467_ == 0)
{
v___x_4462_ = v___x_4353_;
v_isShared_4463_ = v_isSharedCheck_4467_;
goto v_resetjp_4461_;
}
else
{
lean_inc(v_a_4460_);
lean_dec(v___x_4353_);
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
lean_dec(v_a_4346_);
lean_dec_ref(v_xs_4336_);
lean_dec_ref(v___f_4335_);
lean_dec_ref(v___f_4334_);
lean_dec_ref(v_a_4333_);
v_a_4468_ = lean_ctor_get(v___x_4349_, 0);
v_isSharedCheck_4475_ = !lean_is_exclusive(v___x_4349_);
if (v_isSharedCheck_4475_ == 0)
{
v___x_4470_ = v___x_4349_;
v_isShared_4471_ = v_isSharedCheck_4475_;
goto v_resetjp_4469_;
}
else
{
lean_inc(v_a_4468_);
lean_dec(v___x_4349_);
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
lean_dec_ref(v_xs_4336_);
lean_dec_ref(v___f_4335_);
lean_dec_ref(v___f_4334_);
lean_dec_ref(v_a_4333_);
v_a_4476_ = lean_ctor_get(v___x_4345_, 0);
v_isSharedCheck_4483_ = !lean_is_exclusive(v___x_4345_);
if (v_isSharedCheck_4483_ == 0)
{
v___x_4478_ = v___x_4345_;
v_isShared_4479_ = v_isSharedCheck_4483_;
goto v_resetjp_4477_;
}
else
{
lean_inc(v_a_4476_);
lean_dec(v___x_4345_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preprocess___lam__0___boxed(lean_object* v___x_4484_, lean_object* v_a_4485_, lean_object* v___f_4486_, lean_object* v___f_4487_, lean_object* v_xs_4488_, lean_object* v_x_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_, lean_object* v___y_4493_, lean_object* v___y_4494_){
_start:
{
uint8_t v___x_13807__boxed_4495_; lean_object* v_res_4496_; 
v___x_13807__boxed_4495_ = lean_unbox(v___x_4484_);
v_res_4496_ = l_Lean_Elab_WF_preprocess___lam__0(v___x_13807__boxed_4495_, v_a_4485_, v___f_4486_, v___f_4487_, v_xs_4488_, v_x_4489_, v___y_4490_, v___y_4491_, v___y_4492_, v___y_4493_);
lean_dec(v___y_4493_);
lean_dec_ref(v___y_4492_);
lean_dec(v___y_4491_);
lean_dec_ref(v___y_4490_);
lean_dec_ref(v_x_4489_);
return v_res_4496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preprocess(lean_object* v_e_4498_, lean_object* v_a_4499_, lean_object* v_a_4500_, lean_object* v_a_4501_, lean_object* v_a_4502_){
_start:
{
lean_object* v_options_4504_; lean_object* v___x_4505_; uint8_t v___x_4506_; uint8_t v___x_4507_; 
v_options_4504_ = lean_ctor_get(v_a_4501_, 2);
v___x_4505_ = l_wf_preprocess;
v___x_4506_ = l_Lean_Option_get___at___00Lean_Elab_WF_preprocess_spec__1(v_options_4504_, v___x_4505_);
v___x_4507_ = 1;
if (v___x_4506_ == 0)
{
lean_object* v___x_4508_; lean_object* v___x_4509_; lean_object* v___x_4510_; 
v___x_4508_ = lean_box(0);
v___x_4509_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4509_, 0, v_e_4498_);
lean_ctor_set(v___x_4509_, 1, v___x_4508_);
lean_ctor_set_uint8(v___x_4509_, sizeof(void*)*2, v___x_4507_);
v___x_4510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4510_, 0, v___x_4509_);
return v___x_4510_;
}
else
{
lean_object* v___x_4511_; 
v___x_4511_ = l_Lean_Meta_letToHave(v_e_4498_, v_a_4499_, v_a_4500_, v_a_4501_, v_a_4502_);
if (lean_obj_tag(v___x_4511_) == 0)
{
lean_object* v_a_4512_; lean_object* v___f_4513_; lean_object* v___f_4514_; lean_object* v___x_4515_; lean_object* v___f_4516_; uint8_t v___x_4517_; lean_object* v___x_4518_; 
v_a_4512_ = lean_ctor_get(v___x_4511_, 0);
lean_inc(v_a_4512_);
lean_dec_ref(v___x_4511_);
v___f_4513_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___closed__0));
v___f_4514_ = ((lean_object*)(l_Lean_Elab_WF_preprocess___closed__0));
v___x_4515_ = lean_box(v___x_4507_);
lean_inc(v_a_4512_);
v___f_4516_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_preprocess___lam__0___boxed), 11, 4);
lean_closure_set(v___f_4516_, 0, v___x_4515_);
lean_closure_set(v___f_4516_, 1, v_a_4512_);
lean_closure_set(v___f_4516_, 2, v___f_4514_);
lean_closure_set(v___f_4516_, 3, v___f_4513_);
v___x_4517_ = 0;
v___x_4518_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__7___redArg(v_a_4512_, v___f_4516_, v___x_4517_, v_a_4499_, v_a_4500_, v_a_4501_, v_a_4502_);
return v___x_4518_;
}
else
{
lean_object* v_a_4519_; lean_object* v___x_4521_; uint8_t v_isShared_4522_; uint8_t v_isSharedCheck_4526_; 
v_a_4519_ = lean_ctor_get(v___x_4511_, 0);
v_isSharedCheck_4526_ = !lean_is_exclusive(v___x_4511_);
if (v_isSharedCheck_4526_ == 0)
{
v___x_4521_ = v___x_4511_;
v_isShared_4522_ = v_isSharedCheck_4526_;
goto v_resetjp_4520_;
}
else
{
lean_inc(v_a_4519_);
lean_dec(v___x_4511_);
v___x_4521_ = lean_box(0);
v_isShared_4522_ = v_isSharedCheck_4526_;
goto v_resetjp_4520_;
}
v_resetjp_4520_:
{
lean_object* v___x_4524_; 
if (v_isShared_4522_ == 0)
{
v___x_4524_ = v___x_4521_;
goto v_reusejp_4523_;
}
else
{
lean_object* v_reuseFailAlloc_4525_; 
v_reuseFailAlloc_4525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4525_, 0, v_a_4519_);
v___x_4524_ = v_reuseFailAlloc_4525_;
goto v_reusejp_4523_;
}
v_reusejp_4523_:
{
return v___x_4524_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preprocess___boxed(lean_object* v_e_4527_, lean_object* v_a_4528_, lean_object* v_a_4529_, lean_object* v_a_4530_, lean_object* v_a_4531_, lean_object* v_a_4532_){
_start:
{
lean_object* v_res_4533_; 
v_res_4533_ = l_Lean_Elab_WF_preprocess(v_e_4527_, v_a_4528_, v_a_4529_, v_a_4530_, v_a_4531_);
lean_dec(v_a_4531_);
lean_dec_ref(v_a_4530_);
lean_dec(v_a_4529_);
lean_dec_ref(v_a_4528_);
return v_res_4533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0(lean_object* v_x_4534_, lean_object* v_x_4535_, lean_object* v_x_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_, lean_object* v___y_4539_, lean_object* v___y_4540_){
_start:
{
lean_object* v___x_4542_; 
v___x_4542_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0___redArg(v_x_4534_, v_x_4535_, v_x_4536_);
return v___x_4542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0___boxed(lean_object* v_x_4543_, lean_object* v_x_4544_, lean_object* v_x_4545_, lean_object* v___y_4546_, lean_object* v___y_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_, lean_object* v___y_4550_){
_start:
{
lean_object* v_res_4551_; 
v_res_4551_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0(v_x_4543_, v_x_4544_, v_x_4545_, v___y_4546_, v___y_4547_, v___y_4548_, v___y_4549_);
lean_dec(v___y_4549_);
lean_dec_ref(v___y_4548_);
lean_dec(v___y_4547_);
lean_dec_ref(v___y_4546_);
return v_res_4551_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__10_spec__12(lean_object* v_00_u03b1_4552_, lean_object* v_ref_4553_, lean_object* v___y_4554_, lean_object* v___y_4555_){
_start:
{
lean_object* v___x_4557_; 
v___x_4557_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__10_spec__12___redArg(v_ref_4553_);
return v___x_4557_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__10_spec__12___boxed(lean_object* v_00_u03b1_4558_, lean_object* v_ref_4559_, lean_object* v___y_4560_, lean_object* v___y_4561_, lean_object* v___y_4562_){
_start:
{
lean_object* v_res_4563_; 
v_res_4563_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__10_spec__12(v_00_u03b1_4558_, v_ref_4559_, v___y_4560_, v___y_4561_);
lean_dec(v___y_4561_);
lean_dec_ref(v___y_4560_);
return v_res_4563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__10(lean_object* v_00_u03b1_4564_, lean_object* v_x_4565_, lean_object* v___y_4566_, lean_object* v___y_4567_, lean_object* v___y_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_){
_start:
{
lean_object* v___x_4572_; 
lean_inc_ref(v___y_4569_);
v___x_4572_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__10___redArg(v_x_4565_, v___y_4566_, v___y_4567_, v___y_4568_, v___y_4569_, v___y_4570_);
return v___x_4572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__10___boxed(lean_object* v_00_u03b1_4573_, lean_object* v_x_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_, lean_object* v___y_4579_, lean_object* v___y_4580_){
_start:
{
lean_object* v_res_4581_; 
v_res_4581_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__10(v_00_u03b1_4573_, v_x_4574_, v___y_4575_, v___y_4576_, v___y_4577_, v___y_4578_, v___y_4579_);
lean_dec(v___y_4579_);
lean_dec_ref(v___y_4578_);
lean_dec(v___y_4577_);
lean_dec_ref(v___y_4576_);
lean_dec(v___y_4575_);
return v_res_4581_;
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
