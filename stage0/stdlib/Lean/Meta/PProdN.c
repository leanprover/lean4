// Lean compiler output
// Module: Lean.Meta.PProdN
// Imports: public import Lean.Meta.Transform import Init.Data.Range.Polymorphic.Iterators import Init.Omega
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
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isSort(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Expr_sortLevel_x21(lean_object*);
lean_object* lean_array_get_size(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_isAlwaysZero(lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* l_panic___redArg(lean_object*, lean_object*);
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
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_ExprStructEq_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isProj(lean_object*);
lean_object* l_Lean_Expr_projExpr_x21(lean_object*);
lean_object* l_Lean_Expr_projIdx_x21(lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
uint8_t l_IO_CancelToken_isSet(lean_object*);
extern lean_object* l_Lean_interruptExceptionId;
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_expr_dbg_to_string(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ofFn___redArg(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkPProd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "PProd"};
static const lean_object* l_Lean_Meta_mkPProd___closed__0 = (const lean_object*)&l_Lean_Meta_mkPProd___closed__0_value;
static const lean_ctor_object l_Lean_Meta_mkPProd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkPProd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(17, 14, 124, 134, 125, 191, 184, 142)}};
static const lean_object* l_Lean_Meta_mkPProd___closed__1 = (const lean_object*)&l_Lean_Meta_mkPProd___closed__1_value;
static const lean_string_object l_Lean_Meta_mkPProd___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "And"};
static const lean_object* l_Lean_Meta_mkPProd___closed__2 = (const lean_object*)&l_Lean_Meta_mkPProd___closed__2_value;
static const lean_ctor_object l_Lean_Meta_mkPProd___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkPProd___closed__2_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_object* l_Lean_Meta_mkPProd___closed__3 = (const lean_object*)&l_Lean_Meta_mkPProd___closed__3_value;
static lean_once_cell_t l_Lean_Meta_mkPProd___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkPProd___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_mkPProd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkPProd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkPProdMk___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l_Lean_Meta_mkPProdMk___closed__0 = (const lean_object*)&l_Lean_Meta_mkPProdMk___closed__0_value;
static const lean_ctor_object l_Lean_Meta_mkPProdMk___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkPProd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(17, 14, 124, 134, 125, 191, 184, 142)}};
static const lean_ctor_object l_Lean_Meta_mkPProdMk___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkPProdMk___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_mkPProdMk___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 171, 224, 173, 195, 175, 128, 27)}};
static const lean_object* l_Lean_Meta_mkPProdMk___closed__1 = (const lean_object*)&l_Lean_Meta_mkPProdMk___closed__1_value;
static const lean_string_object l_Lean_Meta_mkPProdMk___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "intro"};
static const lean_object* l_Lean_Meta_mkPProdMk___closed__2 = (const lean_object*)&l_Lean_Meta_mkPProdMk___closed__2_value;
static const lean_ctor_object l_Lean_Meta_mkPProdMk___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkPProd___closed__2_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_ctor_object l_Lean_Meta_mkPProdMk___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkPProdMk___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_mkPProdMk___closed__2_value),LEAN_SCALAR_PTR_LITERAL(58, 46, 244, 208, 18, 71, 77, 162)}};
static const lean_object* l_Lean_Meta_mkPProdMk___closed__3 = (const lean_object*)&l_Lean_Meta_mkPProdMk___closed__3_value;
static lean_once_cell_t l_Lean_Meta_mkPProdMk___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkPProdMk___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_mkPProdMk(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkPProdMk___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkPProdFst_spec__0(lean_object*);
static const lean_string_object l_Lean_Meta_mkPProdFst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Lean.Meta.PProdN"};
static const lean_object* l_Lean_Meta_mkPProdFst___closed__0 = (const lean_object*)&l_Lean_Meta_mkPProdFst___closed__0_value;
static const lean_string_object l_Lean_Meta_mkPProdFst___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.Meta.mkPProdFst"};
static const lean_object* l_Lean_Meta_mkPProdFst___closed__1 = (const lean_object*)&l_Lean_Meta_mkPProdFst___closed__1_value;
static const lean_string_object l_Lean_Meta_mkPProdFst___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "mkPProdFst: cannot handle "};
static const lean_object* l_Lean_Meta_mkPProdFst___closed__2 = (const lean_object*)&l_Lean_Meta_mkPProdFst___closed__2_value;
static const lean_string_object l_Lean_Meta_mkPProdFst___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "\nof type "};
static const lean_object* l_Lean_Meta_mkPProdFst___closed__3 = (const lean_object*)&l_Lean_Meta_mkPProdFst___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkPProdFst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkPProdFstM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkPProdFstM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_PProdN_0__Lean_Meta_mkTypeSnd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "_private.Lean.Meta.PProdN.0.Lean.Meta.mkTypeSnd"};
static const lean_object* l___private_Lean_Meta_PProdN_0__Lean_Meta_mkTypeSnd___closed__0 = (const lean_object*)&l___private_Lean_Meta_PProdN_0__Lean_Meta_mkTypeSnd___closed__0_value;
static const lean_string_object l___private_Lean_Meta_PProdN_0__Lean_Meta_mkTypeSnd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "mkTypeSnd: cannot handle type "};
static const lean_object* l___private_Lean_Meta_PProdN_0__Lean_Meta_mkTypeSnd___closed__1 = (const lean_object*)&l___private_Lean_Meta_PProdN_0__Lean_Meta_mkTypeSnd___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_PProdN_0__Lean_Meta_mkTypeSnd(lean_object*);
static const lean_string_object l_Lean_Meta_mkPProdSnd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.Meta.mkPProdSnd"};
static const lean_object* l_Lean_Meta_mkPProdSnd___closed__0 = (const lean_object*)&l_Lean_Meta_mkPProdSnd___closed__0_value;
static const lean_string_object l_Lean_Meta_mkPProdSnd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "mkPProdSnd: cannot handle "};
static const lean_object* l_Lean_Meta_mkPProdSnd___closed__1 = (const lean_object*)&l_Lean_Meta_mkPProdSnd___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkPProdSnd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkPProdSndM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkPProdSndM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_PProdN_genMk___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_PProdN_genMk___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_PProdN_genMk___redArg___closed__0_value;
static const lean_string_object l_Lean_Meta_PProdN_genMk___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.Meta.PProdN.genMk"};
static const lean_object* l_Lean_Meta_PProdN_genMk___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_PProdN_genMk___redArg___closed__1_value;
static const lean_string_object l_Lean_Meta_PProdN_genMk___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "assertion violation: !xs.isEmpty\n  "};
static const lean_object* l_Lean_Meta_PProdN_genMk___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_PProdN_genMk___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Meta_PProdN_genMk___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_PProdN_genMk___redArg___closed__3;
static lean_once_cell_t l_Lean_Meta_PProdN_genMk___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_PProdN_genMk___redArg___closed__4;
static lean_once_cell_t l_Lean_Meta_PProdN_genMk___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_PProdN_genMk___redArg___closed__5;
static const lean_closure_object l_Lean_Meta_PProdN_genMk___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_PProdN_genMk___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_PProdN_genMk___redArg___closed__6_value;
static const lean_closure_object l_Lean_Meta_PProdN_genMk___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_PProdN_genMk___redArg___closed__7 = (const lean_object*)&l_Lean_Meta_PProdN_genMk___redArg___closed__7_value;
static const lean_closure_object l_Lean_Meta_PProdN_genMk___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_PProdN_genMk___redArg___closed__8 = (const lean_object*)&l_Lean_Meta_PProdN_genMk___redArg___closed__8_value;
static const lean_closure_object l_Lean_Meta_PProdN_genMk___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_PProdN_genMk___redArg___closed__9 = (const lean_object*)&l_Lean_Meta_PProdN_genMk___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_genMk___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_genMk___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_genMk(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_genMk___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_PProdN_pack___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_mkPProd___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_PProdN_pack___closed__0 = (const lean_object*)&l_Lean_Meta_PProdN_pack___closed__0_value;
static const lean_string_object l_Lean_Meta_PProdN_pack___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "PUnit"};
static const lean_object* l_Lean_Meta_PProdN_pack___closed__1 = (const lean_object*)&l_Lean_Meta_PProdN_pack___closed__1_value;
static const lean_ctor_object l_Lean_Meta_PProdN_pack___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_PProdN_pack___closed__1_value),LEAN_SCALAR_PTR_LITERAL(23, 153, 158, 141, 176, 162, 235, 153)}};
static const lean_object* l_Lean_Meta_PProdN_pack___closed__2 = (const lean_object*)&l_Lean_Meta_PProdN_pack___closed__2_value;
static const lean_string_object l_Lean_Meta_PProdN_pack___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "True"};
static const lean_object* l_Lean_Meta_PProdN_pack___closed__3 = (const lean_object*)&l_Lean_Meta_PProdN_pack___closed__3_value;
static const lean_ctor_object l_Lean_Meta_PProdN_pack___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_PProdN_pack___closed__3_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_object* l_Lean_Meta_PProdN_pack___closed__4 = (const lean_object*)&l_Lean_Meta_PProdN_pack___closed__4_value;
static lean_once_cell_t l_Lean_Meta_PProdN_pack___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_PProdN_pack___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_pack(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_pack___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_unpack_go___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_unpack_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_unpack_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_unpack_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_PProdN_unpack___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_PProdN_unpack___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_PProdN_unpack___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_unpack___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_unpack___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_unpack(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_unpack___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_PProdN_mk___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_mkPProdMk___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_PProdN_mk___closed__0 = (const lean_object*)&l_Lean_Meta_PProdN_mk___closed__0_value;
static const lean_string_object l_Lean_Meta_PProdN_mk___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "unit"};
static const lean_object* l_Lean_Meta_PProdN_mk___closed__1 = (const lean_object*)&l_Lean_Meta_PProdN_mk___closed__1_value;
static const lean_ctor_object l_Lean_Meta_PProdN_mk___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_PProdN_pack___closed__1_value),LEAN_SCALAR_PTR_LITERAL(23, 153, 158, 141, 176, 162, 235, 153)}};
static const lean_ctor_object l_Lean_Meta_PProdN_mk___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_PProdN_mk___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_PProdN_mk___closed__1_value),LEAN_SCALAR_PTR_LITERAL(146, 91, 82, 196, 249, 72, 203, 194)}};
static const lean_object* l_Lean_Meta_PProdN_mk___closed__2 = (const lean_object*)&l_Lean_Meta_PProdN_mk___closed__2_value;
static const lean_ctor_object l_Lean_Meta_PProdN_mk___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_PProdN_pack___closed__3_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_ctor_object l_Lean_Meta_PProdN_mk___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_PProdN_mk___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_mkPProdMk___closed__2_value),LEAN_SCALAR_PTR_LITERAL(177, 152, 123, 219, 220, 182, 189, 250)}};
static const lean_object* l_Lean_Meta_PProdN_mk___closed__3 = (const lean_object*)&l_Lean_Meta_PProdN_mk___closed__3_value;
static lean_once_cell_t l_Lean_Meta_PProdN_mk___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_PProdN_mk___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_mk(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_mk___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_proj_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_proj_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_proj(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_proj___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_proj_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_proj_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_projs___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_projs___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_projs(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_projM_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_projM_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_projM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_projM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_projM_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_projM_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_PProdN_packLambdas_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_PProdN_packLambdas_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_PProdN_packLambdas_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_PProdN_packLambdas_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_PProdN_packLambdas___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.Meta.PProdN.packLambdas"};
static const lean_object* l_Lean_Meta_PProdN_packLambdas___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_PProdN_packLambdas___lam__0___closed__0_value;
static const lean_string_object l_Lean_Meta_PProdN_packLambdas___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 159, .m_capacity = 159, .m_length = 158, .m_data = "assertion violation: sort.isSort\n    -- NB: Use beta, not instantiateLambda; when constructing the belowDict below\n    -- we pass `C`, a plain FVar, here\n    "};
static const lean_object* l_Lean_Meta_PProdN_packLambdas___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_PProdN_packLambdas___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Meta_PProdN_packLambdas___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_PProdN_packLambdas___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_packLambdas___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_packLambdas___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_packLambdas(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_packLambdas___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_mkLambdas___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_mkLambdas___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_mkLambdas(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_mkLambdas___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_stripProjs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_stripProjs___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_reduceProjs___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_reduceProjs___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "right"};
static const lean_object* l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkPProd___closed__2_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_ctor_object l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 204, 165, 192, 253, 41, 237, 145)}};
static const lean_object* l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__1 = (const lean_object*)&l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__1_value;
static const lean_string_object l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "snd"};
static const lean_object* l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__2 = (const lean_object*)&l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__2_value;
static const lean_ctor_object l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkPProd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(17, 14, 124, 134, 125, 191, 184, 142)}};
static const lean_ctor_object l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(43, 95, 219, 7, 221, 204, 133, 76)}};
static const lean_object* l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__3 = (const lean_object*)&l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__3_value;
static const lean_string_object l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "left"};
static const lean_object* l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__4 = (const lean_object*)&l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__4_value;
static const lean_ctor_object l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkPProd___closed__2_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_ctor_object l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(12, 252, 227, 83, 88, 185, 40, 148)}};
static const lean_object* l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__5 = (const lean_object*)&l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__5_value;
static const lean_string_object l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fst"};
static const lean_object* l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__6 = (const lean_object*)&l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__6_value;
static const lean_ctor_object l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkPProd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(17, 14, 124, 134, 125, 191, 184, 142)}};
static const lean_ctor_object l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(50, 180, 76, 247, 52, 250, 163, 59)}};
static const lean_object* l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__7 = (const lean_object*)&l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_reduceProjs___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_reduceProjs___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__12___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__10___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__8___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__8___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__8___redArg();
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__8___redArg___boxed(lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "transform"};
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__1___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__0;
static lean_once_cell_t l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__1;
static lean_once_cell_t l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_PProdN_reduceProjs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_PProdN_reduceProjs___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_PProdN_reduceProjs___closed__0 = (const lean_object*)&l_Lean_Meta_PProdN_reduceProjs___closed__0_value;
static const lean_closure_object l_Lean_Meta_PProdN_reduceProjs___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_PProdN_reduceProjs___lam__1___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_PProdN_reduceProjs___closed__1 = (const lean_object*)&l_Lean_Meta_PProdN_reduceProjs___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_reduceProjs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_reduceProjs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_mkPProd___closed__4(void){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_7_ = lean_box(0);
v___x_8_ = ((lean_object*)(l_Lean_Meta_mkPProd___closed__3));
v___x_9_ = l_Lean_Expr_const___override(v___x_8_, v___x_7_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPProd(lean_object* v_e1_10_, lean_object* v_e2_11_, lean_object* v_a_12_, lean_object* v_a_13_, lean_object* v_a_14_, lean_object* v_a_15_){
_start:
{
lean_object* v___x_17_; 
lean_inc_ref(v_e1_10_);
v___x_17_ = l_Lean_Meta_getLevel(v_e1_10_, v_a_12_, v_a_13_, v_a_14_, v_a_15_);
if (lean_obj_tag(v___x_17_) == 0)
{
lean_object* v_a_18_; lean_object* v___x_19_; 
v_a_18_ = lean_ctor_get(v___x_17_, 0);
lean_inc(v_a_18_);
lean_dec_ref_known(v___x_17_, 1);
lean_inc_ref(v_e2_11_);
v___x_19_ = l_Lean_Meta_getLevel(v_e2_11_, v_a_12_, v_a_13_, v_a_14_, v_a_15_);
if (lean_obj_tag(v___x_19_) == 0)
{
lean_object* v_a_20_; lean_object* v___x_22_; uint8_t v_isShared_23_; uint8_t v_isSharedCheck_42_; 
v_a_20_ = lean_ctor_get(v___x_19_, 0);
v_isSharedCheck_42_ = !lean_is_exclusive(v___x_19_);
if (v_isSharedCheck_42_ == 0)
{
v___x_22_ = v___x_19_;
v_isShared_23_ = v_isSharedCheck_42_;
goto v_resetjp_21_;
}
else
{
lean_inc(v_a_20_);
lean_dec(v___x_19_);
v___x_22_ = lean_box(0);
v_isShared_23_ = v_isSharedCheck_42_;
goto v_resetjp_21_;
}
v_resetjp_21_:
{
uint8_t v___y_25_; uint8_t v___x_40_; 
v___x_40_ = l_Lean_Level_isAlwaysZero(v_a_18_);
if (v___x_40_ == 0)
{
v___y_25_ = v___x_40_;
goto v___jp_24_;
}
else
{
uint8_t v___x_41_; 
v___x_41_ = l_Lean_Level_isAlwaysZero(v_a_20_);
v___y_25_ = v___x_41_;
goto v___jp_24_;
}
v___jp_24_:
{
if (v___y_25_ == 0)
{
lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_33_; 
v___x_26_ = ((lean_object*)(l_Lean_Meta_mkPProd___closed__1));
v___x_27_ = lean_box(0);
v___x_28_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_28_, 0, v_a_20_);
lean_ctor_set(v___x_28_, 1, v___x_27_);
v___x_29_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_29_, 0, v_a_18_);
lean_ctor_set(v___x_29_, 1, v___x_28_);
v___x_30_ = l_Lean_Expr_const___override(v___x_26_, v___x_29_);
v___x_31_ = l_Lean_mkAppB(v___x_30_, v_e1_10_, v_e2_11_);
if (v_isShared_23_ == 0)
{
lean_ctor_set(v___x_22_, 0, v___x_31_);
v___x_33_ = v___x_22_;
goto v_reusejp_32_;
}
else
{
lean_object* v_reuseFailAlloc_34_; 
v_reuseFailAlloc_34_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_34_, 0, v___x_31_);
v___x_33_ = v_reuseFailAlloc_34_;
goto v_reusejp_32_;
}
v_reusejp_32_:
{
return v___x_33_;
}
}
else
{
lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_38_; 
lean_dec(v_a_20_);
lean_dec(v_a_18_);
v___x_35_ = lean_obj_once(&l_Lean_Meta_mkPProd___closed__4, &l_Lean_Meta_mkPProd___closed__4_once, _init_l_Lean_Meta_mkPProd___closed__4);
v___x_36_ = l_Lean_mkAppB(v___x_35_, v_e1_10_, v_e2_11_);
if (v_isShared_23_ == 0)
{
lean_ctor_set(v___x_22_, 0, v___x_36_);
v___x_38_ = v___x_22_;
goto v_reusejp_37_;
}
else
{
lean_object* v_reuseFailAlloc_39_; 
v_reuseFailAlloc_39_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_39_, 0, v___x_36_);
v___x_38_ = v_reuseFailAlloc_39_;
goto v_reusejp_37_;
}
v_reusejp_37_:
{
return v___x_38_;
}
}
}
}
}
else
{
lean_object* v_a_43_; lean_object* v___x_45_; uint8_t v_isShared_46_; uint8_t v_isSharedCheck_50_; 
lean_dec(v_a_18_);
lean_dec_ref(v_e2_11_);
lean_dec_ref(v_e1_10_);
v_a_43_ = lean_ctor_get(v___x_19_, 0);
v_isSharedCheck_50_ = !lean_is_exclusive(v___x_19_);
if (v_isSharedCheck_50_ == 0)
{
v___x_45_ = v___x_19_;
v_isShared_46_ = v_isSharedCheck_50_;
goto v_resetjp_44_;
}
else
{
lean_inc(v_a_43_);
lean_dec(v___x_19_);
v___x_45_ = lean_box(0);
v_isShared_46_ = v_isSharedCheck_50_;
goto v_resetjp_44_;
}
v_resetjp_44_:
{
lean_object* v___x_48_; 
if (v_isShared_46_ == 0)
{
v___x_48_ = v___x_45_;
goto v_reusejp_47_;
}
else
{
lean_object* v_reuseFailAlloc_49_; 
v_reuseFailAlloc_49_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_49_, 0, v_a_43_);
v___x_48_ = v_reuseFailAlloc_49_;
goto v_reusejp_47_;
}
v_reusejp_47_:
{
return v___x_48_;
}
}
}
}
else
{
lean_object* v_a_51_; lean_object* v___x_53_; uint8_t v_isShared_54_; uint8_t v_isSharedCheck_58_; 
lean_dec_ref(v_e2_11_);
lean_dec_ref(v_e1_10_);
v_a_51_ = lean_ctor_get(v___x_17_, 0);
v_isSharedCheck_58_ = !lean_is_exclusive(v___x_17_);
if (v_isSharedCheck_58_ == 0)
{
v___x_53_ = v___x_17_;
v_isShared_54_ = v_isSharedCheck_58_;
goto v_resetjp_52_;
}
else
{
lean_inc(v_a_51_);
lean_dec(v___x_17_);
v___x_53_ = lean_box(0);
v_isShared_54_ = v_isSharedCheck_58_;
goto v_resetjp_52_;
}
v_resetjp_52_:
{
lean_object* v___x_56_; 
if (v_isShared_54_ == 0)
{
v___x_56_ = v___x_53_;
goto v_reusejp_55_;
}
else
{
lean_object* v_reuseFailAlloc_57_; 
v_reuseFailAlloc_57_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_57_, 0, v_a_51_);
v___x_56_ = v_reuseFailAlloc_57_;
goto v_reusejp_55_;
}
v_reusejp_55_:
{
return v___x_56_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPProd___boxed(lean_object* v_e1_59_, lean_object* v_e2_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l_Lean_Meta_mkPProd(v_e1_59_, v_e2_60_, v_a_61_, v_a_62_, v_a_63_, v_a_64_);
lean_dec(v_a_64_);
lean_dec_ref(v_a_63_);
lean_dec(v_a_62_);
lean_dec_ref(v_a_61_);
return v_res_66_;
}
}
static lean_object* _init_l_Lean_Meta_mkPProdMk___closed__4(void){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_75_ = lean_box(0);
v___x_76_ = ((lean_object*)(l_Lean_Meta_mkPProdMk___closed__3));
v___x_77_ = l_Lean_Expr_const___override(v___x_76_, v___x_75_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPProdMk(lean_object* v_e1_78_, lean_object* v_e2_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_){
_start:
{
lean_object* v___x_85_; 
lean_inc(v_a_83_);
lean_inc_ref(v_a_82_);
lean_inc(v_a_81_);
lean_inc_ref(v_a_80_);
lean_inc_ref(v_e1_78_);
v___x_85_ = lean_infer_type(v_e1_78_, v_a_80_, v_a_81_, v_a_82_, v_a_83_);
if (lean_obj_tag(v___x_85_) == 0)
{
lean_object* v_a_86_; lean_object* v___x_87_; 
v_a_86_ = lean_ctor_get(v___x_85_, 0);
lean_inc(v_a_86_);
lean_dec_ref_known(v___x_85_, 1);
lean_inc(v_a_83_);
lean_inc_ref(v_a_82_);
lean_inc(v_a_81_);
lean_inc_ref(v_a_80_);
lean_inc_ref(v_e2_79_);
v___x_87_ = lean_infer_type(v_e2_79_, v_a_80_, v_a_81_, v_a_82_, v_a_83_);
if (lean_obj_tag(v___x_87_) == 0)
{
lean_object* v_a_88_; lean_object* v___x_89_; 
v_a_88_ = lean_ctor_get(v___x_87_, 0);
lean_inc(v_a_88_);
lean_dec_ref_known(v___x_87_, 1);
lean_inc(v_a_86_);
v___x_89_ = l_Lean_Meta_getLevel(v_a_86_, v_a_80_, v_a_81_, v_a_82_, v_a_83_);
if (lean_obj_tag(v___x_89_) == 0)
{
lean_object* v_a_90_; lean_object* v___x_91_; 
v_a_90_ = lean_ctor_get(v___x_89_, 0);
lean_inc(v_a_90_);
lean_dec_ref_known(v___x_89_, 1);
lean_inc(v_a_88_);
v___x_91_ = l_Lean_Meta_getLevel(v_a_88_, v_a_80_, v_a_81_, v_a_82_, v_a_83_);
if (lean_obj_tag(v___x_91_) == 0)
{
lean_object* v_a_92_; lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_114_; 
v_a_92_ = lean_ctor_get(v___x_91_, 0);
v_isSharedCheck_114_ = !lean_is_exclusive(v___x_91_);
if (v_isSharedCheck_114_ == 0)
{
v___x_94_ = v___x_91_;
v_isShared_95_ = v_isSharedCheck_114_;
goto v_resetjp_93_;
}
else
{
lean_inc(v_a_92_);
lean_dec(v___x_91_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_114_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
uint8_t v___y_97_; uint8_t v___x_112_; 
v___x_112_ = l_Lean_Level_isAlwaysZero(v_a_90_);
if (v___x_112_ == 0)
{
v___y_97_ = v___x_112_;
goto v___jp_96_;
}
else
{
uint8_t v___x_113_; 
v___x_113_ = l_Lean_Level_isAlwaysZero(v_a_92_);
v___y_97_ = v___x_113_;
goto v___jp_96_;
}
v___jp_96_:
{
if (v___y_97_ == 0)
{
lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_105_; 
v___x_98_ = ((lean_object*)(l_Lean_Meta_mkPProdMk___closed__1));
v___x_99_ = lean_box(0);
v___x_100_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_100_, 0, v_a_92_);
lean_ctor_set(v___x_100_, 1, v___x_99_);
v___x_101_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_101_, 0, v_a_90_);
lean_ctor_set(v___x_101_, 1, v___x_100_);
v___x_102_ = l_Lean_Expr_const___override(v___x_98_, v___x_101_);
v___x_103_ = l_Lean_mkApp4(v___x_102_, v_a_86_, v_a_88_, v_e1_78_, v_e2_79_);
if (v_isShared_95_ == 0)
{
lean_ctor_set(v___x_94_, 0, v___x_103_);
v___x_105_ = v___x_94_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v___x_103_);
v___x_105_ = v_reuseFailAlloc_106_;
goto v_reusejp_104_;
}
v_reusejp_104_:
{
return v___x_105_;
}
}
else
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_110_; 
lean_dec(v_a_92_);
lean_dec(v_a_90_);
v___x_107_ = lean_obj_once(&l_Lean_Meta_mkPProdMk___closed__4, &l_Lean_Meta_mkPProdMk___closed__4_once, _init_l_Lean_Meta_mkPProdMk___closed__4);
v___x_108_ = l_Lean_mkApp4(v___x_107_, v_a_86_, v_a_88_, v_e1_78_, v_e2_79_);
if (v_isShared_95_ == 0)
{
lean_ctor_set(v___x_94_, 0, v___x_108_);
v___x_110_ = v___x_94_;
goto v_reusejp_109_;
}
else
{
lean_object* v_reuseFailAlloc_111_; 
v_reuseFailAlloc_111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_111_, 0, v___x_108_);
v___x_110_ = v_reuseFailAlloc_111_;
goto v_reusejp_109_;
}
v_reusejp_109_:
{
return v___x_110_;
}
}
}
}
}
else
{
lean_object* v_a_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_122_; 
lean_dec(v_a_90_);
lean_dec(v_a_88_);
lean_dec(v_a_86_);
lean_dec_ref(v_e2_79_);
lean_dec_ref(v_e1_78_);
v_a_115_ = lean_ctor_get(v___x_91_, 0);
v_isSharedCheck_122_ = !lean_is_exclusive(v___x_91_);
if (v_isSharedCheck_122_ == 0)
{
v___x_117_ = v___x_91_;
v_isShared_118_ = v_isSharedCheck_122_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_a_115_);
lean_dec(v___x_91_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_122_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
lean_object* v___x_120_; 
if (v_isShared_118_ == 0)
{
v___x_120_ = v___x_117_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v_a_115_);
v___x_120_ = v_reuseFailAlloc_121_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
return v___x_120_;
}
}
}
}
else
{
lean_object* v_a_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_130_; 
lean_dec(v_a_88_);
lean_dec(v_a_86_);
lean_dec_ref(v_e2_79_);
lean_dec_ref(v_e1_78_);
v_a_123_ = lean_ctor_get(v___x_89_, 0);
v_isSharedCheck_130_ = !lean_is_exclusive(v___x_89_);
if (v_isSharedCheck_130_ == 0)
{
v___x_125_ = v___x_89_;
v_isShared_126_ = v_isSharedCheck_130_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_a_123_);
lean_dec(v___x_89_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_130_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v___x_128_; 
if (v_isShared_126_ == 0)
{
v___x_128_ = v___x_125_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v_a_123_);
v___x_128_ = v_reuseFailAlloc_129_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
return v___x_128_;
}
}
}
}
else
{
lean_dec(v_a_86_);
lean_dec_ref(v_e2_79_);
lean_dec_ref(v_e1_78_);
return v___x_87_;
}
}
else
{
lean_dec_ref(v_e2_79_);
lean_dec_ref(v_e1_78_);
return v___x_85_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPProdMk___boxed(lean_object* v_e1_131_, lean_object* v_e2_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Lean_Meta_mkPProdMk(v_e1_131_, v_e2_132_, v_a_133_, v_a_134_, v_a_135_, v_a_136_);
lean_dec(v_a_136_);
lean_dec_ref(v_a_135_);
lean_dec(v_a_134_);
lean_dec_ref(v_a_133_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkPProdFst_spec__0(lean_object* v_msg_139_){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_140_ = l_Lean_instInhabitedExpr;
v___x_141_ = lean_panic_fn_borrowed(v___x_140_, v_msg_139_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPProdFst(lean_object* v_t_146_, lean_object* v_e_147_){
_start:
{
lean_object* v___x_162_; uint8_t v___x_163_; 
lean_inc_ref(v_t_146_);
v___x_162_ = l_Lean_Expr_cleanupAnnotations(v_t_146_);
v___x_163_ = l_Lean_Expr_isApp(v___x_162_);
if (v___x_163_ == 0)
{
lean_dec_ref(v___x_162_);
goto v___jp_148_;
}
else
{
lean_object* v___x_164_; uint8_t v___x_165_; 
v___x_164_ = l_Lean_Expr_appFnCleanup___redArg(v___x_162_);
v___x_165_ = l_Lean_Expr_isApp(v___x_164_);
if (v___x_165_ == 0)
{
lean_dec_ref(v___x_164_);
goto v___jp_148_;
}
else
{
lean_object* v___x_166_; lean_object* v___x_167_; uint8_t v___x_168_; 
v___x_166_ = l_Lean_Expr_appFnCleanup___redArg(v___x_164_);
v___x_167_ = ((lean_object*)(l_Lean_Meta_mkPProd___closed__3));
v___x_168_ = l_Lean_Expr_isConstOf(v___x_166_, v___x_167_);
if (v___x_168_ == 0)
{
lean_object* v___x_169_; uint8_t v___x_170_; 
v___x_169_ = ((lean_object*)(l_Lean_Meta_mkPProd___closed__1));
v___x_170_ = l_Lean_Expr_isConstOf(v___x_166_, v___x_169_);
lean_dec_ref(v___x_166_);
if (v___x_170_ == 0)
{
goto v___jp_148_;
}
else
{
lean_object* v___x_171_; lean_object* v___x_172_; 
lean_dec_ref(v_t_146_);
v___x_171_ = lean_unsigned_to_nat(0u);
v___x_172_ = l_Lean_Expr_proj___override(v___x_169_, v___x_171_, v_e_147_);
return v___x_172_;
}
}
else
{
lean_object* v___x_173_; lean_object* v___x_174_; 
lean_dec_ref(v___x_166_);
lean_dec_ref(v_t_146_);
v___x_173_ = lean_unsigned_to_nat(0u);
v___x_174_ = l_Lean_Expr_proj___override(v___x_167_, v___x_173_, v_e_147_);
return v___x_174_;
}
}
}
v___jp_148_:
{
lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_149_ = ((lean_object*)(l_Lean_Meta_mkPProdFst___closed__0));
v___x_150_ = ((lean_object*)(l_Lean_Meta_mkPProdFst___closed__1));
v___x_151_ = lean_unsigned_to_nat(60u);
v___x_152_ = lean_unsigned_to_nat(9u);
v___x_153_ = ((lean_object*)(l_Lean_Meta_mkPProdFst___closed__2));
v___x_154_ = lean_expr_dbg_to_string(v_e_147_);
lean_dec_ref(v_e_147_);
v___x_155_ = lean_string_append(v___x_153_, v___x_154_);
lean_dec_ref(v___x_154_);
v___x_156_ = ((lean_object*)(l_Lean_Meta_mkPProdFst___closed__3));
v___x_157_ = lean_string_append(v___x_155_, v___x_156_);
v___x_158_ = lean_expr_dbg_to_string(v_t_146_);
lean_dec_ref(v_t_146_);
v___x_159_ = lean_string_append(v___x_157_, v___x_158_);
lean_dec_ref(v___x_158_);
v___x_160_ = l_mkPanicMessageWithDecl(v___x_149_, v___x_150_, v___x_151_, v___x_152_, v___x_159_);
lean_dec_ref(v___x_159_);
v___x_161_ = l_panic___at___00Lean_Meta_mkPProdFst_spec__0(v___x_160_);
return v___x_161_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPProdFstM(lean_object* v_e_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_){
_start:
{
lean_object* v___x_181_; 
lean_inc(v_a_179_);
lean_inc_ref(v_a_178_);
lean_inc(v_a_177_);
lean_inc_ref(v_a_176_);
lean_inc_ref(v_e_175_);
v___x_181_ = lean_infer_type(v_e_175_, v_a_176_, v_a_177_, v_a_178_, v_a_179_);
if (lean_obj_tag(v___x_181_) == 0)
{
lean_object* v_a_182_; lean_object* v___x_183_; 
v_a_182_ = lean_ctor_get(v___x_181_, 0);
lean_inc(v_a_182_);
lean_dec_ref_known(v___x_181_, 1);
lean_inc(v_a_179_);
lean_inc_ref(v_a_178_);
lean_inc(v_a_177_);
lean_inc_ref(v_a_176_);
v___x_183_ = lean_whnf(v_a_182_, v_a_176_, v_a_177_, v_a_178_, v_a_179_);
if (lean_obj_tag(v___x_183_) == 0)
{
lean_object* v_a_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_192_; 
v_a_184_ = lean_ctor_get(v___x_183_, 0);
v_isSharedCheck_192_ = !lean_is_exclusive(v___x_183_);
if (v_isSharedCheck_192_ == 0)
{
v___x_186_ = v___x_183_;
v_isShared_187_ = v_isSharedCheck_192_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_a_184_);
lean_dec(v___x_183_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_192_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v___x_188_; lean_object* v___x_190_; 
v___x_188_ = l_Lean_Meta_mkPProdFst(v_a_184_, v_e_175_);
if (v_isShared_187_ == 0)
{
lean_ctor_set(v___x_186_, 0, v___x_188_);
v___x_190_ = v___x_186_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v___x_188_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
return v___x_190_;
}
}
}
else
{
lean_dec_ref(v_e_175_);
return v___x_183_;
}
}
else
{
lean_dec_ref(v_e_175_);
return v___x_181_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPProdFstM___boxed(lean_object* v_e_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l_Lean_Meta_mkPProdFstM(v_e_193_, v_a_194_, v_a_195_, v_a_196_, v_a_197_);
lean_dec(v_a_197_);
lean_dec_ref(v_a_196_);
lean_dec(v_a_195_);
lean_dec_ref(v_a_194_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PProdN_0__Lean_Meta_mkTypeSnd(lean_object* v_t_202_){
_start:
{
lean_object* v___x_213_; uint8_t v___x_214_; 
lean_inc_ref(v_t_202_);
v___x_213_ = l_Lean_Expr_cleanupAnnotations(v_t_202_);
v___x_214_ = l_Lean_Expr_isApp(v___x_213_);
if (v___x_214_ == 0)
{
lean_dec_ref(v___x_213_);
goto v___jp_203_;
}
else
{
lean_object* v_arg_215_; lean_object* v___x_216_; uint8_t v___x_217_; 
v_arg_215_ = lean_ctor_get(v___x_213_, 1);
lean_inc_ref(v_arg_215_);
v___x_216_ = l_Lean_Expr_appFnCleanup___redArg(v___x_213_);
v___x_217_ = l_Lean_Expr_isApp(v___x_216_);
if (v___x_217_ == 0)
{
lean_dec_ref(v___x_216_);
lean_dec_ref(v_arg_215_);
goto v___jp_203_;
}
else
{
lean_object* v___x_218_; lean_object* v___x_219_; uint8_t v___x_220_; 
v___x_218_ = l_Lean_Expr_appFnCleanup___redArg(v___x_216_);
v___x_219_ = ((lean_object*)(l_Lean_Meta_mkPProd___closed__3));
v___x_220_ = l_Lean_Expr_isConstOf(v___x_218_, v___x_219_);
if (v___x_220_ == 0)
{
lean_object* v___x_221_; uint8_t v___x_222_; 
v___x_221_ = ((lean_object*)(l_Lean_Meta_mkPProd___closed__1));
v___x_222_ = l_Lean_Expr_isConstOf(v___x_218_, v___x_221_);
lean_dec_ref(v___x_218_);
if (v___x_222_ == 0)
{
lean_dec_ref(v_arg_215_);
goto v___jp_203_;
}
else
{
lean_dec_ref(v_t_202_);
return v_arg_215_;
}
}
else
{
lean_dec_ref(v___x_218_);
lean_dec_ref(v_t_202_);
return v_arg_215_;
}
}
}
v___jp_203_:
{
lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_204_ = ((lean_object*)(l_Lean_Meta_mkPProdFst___closed__0));
v___x_205_ = ((lean_object*)(l___private_Lean_Meta_PProdN_0__Lean_Meta_mkTypeSnd___closed__0));
v___x_206_ = lean_unsigned_to_nat(70u);
v___x_207_ = lean_unsigned_to_nat(9u);
v___x_208_ = ((lean_object*)(l___private_Lean_Meta_PProdN_0__Lean_Meta_mkTypeSnd___closed__1));
v___x_209_ = lean_expr_dbg_to_string(v_t_202_);
lean_dec_ref(v_t_202_);
v___x_210_ = lean_string_append(v___x_208_, v___x_209_);
lean_dec_ref(v___x_209_);
v___x_211_ = l_mkPanicMessageWithDecl(v___x_204_, v___x_205_, v___x_206_, v___x_207_, v___x_210_);
lean_dec_ref(v___x_210_);
v___x_212_ = l_panic___at___00Lean_Meta_mkPProdFst_spec__0(v___x_211_);
return v___x_212_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPProdSnd(lean_object* v_t_225_, lean_object* v_e_226_){
_start:
{
lean_object* v___x_241_; uint8_t v___x_242_; 
lean_inc_ref(v_t_225_);
v___x_241_ = l_Lean_Expr_cleanupAnnotations(v_t_225_);
v___x_242_ = l_Lean_Expr_isApp(v___x_241_);
if (v___x_242_ == 0)
{
lean_dec_ref(v___x_241_);
goto v___jp_227_;
}
else
{
lean_object* v___x_243_; uint8_t v___x_244_; 
v___x_243_ = l_Lean_Expr_appFnCleanup___redArg(v___x_241_);
v___x_244_ = l_Lean_Expr_isApp(v___x_243_);
if (v___x_244_ == 0)
{
lean_dec_ref(v___x_243_);
goto v___jp_227_;
}
else
{
lean_object* v___x_245_; lean_object* v___x_246_; uint8_t v___x_247_; 
v___x_245_ = l_Lean_Expr_appFnCleanup___redArg(v___x_243_);
v___x_246_ = ((lean_object*)(l_Lean_Meta_mkPProd___closed__3));
v___x_247_ = l_Lean_Expr_isConstOf(v___x_245_, v___x_246_);
if (v___x_247_ == 0)
{
lean_object* v___x_248_; uint8_t v___x_249_; 
v___x_248_ = ((lean_object*)(l_Lean_Meta_mkPProd___closed__1));
v___x_249_ = l_Lean_Expr_isConstOf(v___x_245_, v___x_248_);
lean_dec_ref(v___x_245_);
if (v___x_249_ == 0)
{
goto v___jp_227_;
}
else
{
lean_object* v___x_250_; lean_object* v___x_251_; 
lean_dec_ref(v_t_225_);
v___x_250_ = lean_unsigned_to_nat(1u);
v___x_251_ = l_Lean_Expr_proj___override(v___x_248_, v___x_250_, v_e_226_);
return v___x_251_;
}
}
else
{
lean_object* v___x_252_; lean_object* v___x_253_; 
lean_dec_ref(v___x_245_);
lean_dec_ref(v_t_225_);
v___x_252_ = lean_unsigned_to_nat(1u);
v___x_253_ = l_Lean_Expr_proj___override(v___x_246_, v___x_252_, v_e_226_);
return v___x_253_;
}
}
}
v___jp_227_:
{
lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_228_ = ((lean_object*)(l_Lean_Meta_mkPProdFst___closed__0));
v___x_229_ = ((lean_object*)(l_Lean_Meta_mkPProdSnd___closed__0));
v___x_230_ = lean_unsigned_to_nat(77u);
v___x_231_ = lean_unsigned_to_nat(9u);
v___x_232_ = ((lean_object*)(l_Lean_Meta_mkPProdSnd___closed__1));
v___x_233_ = lean_expr_dbg_to_string(v_e_226_);
lean_dec_ref(v_e_226_);
v___x_234_ = lean_string_append(v___x_232_, v___x_233_);
lean_dec_ref(v___x_233_);
v___x_235_ = ((lean_object*)(l_Lean_Meta_mkPProdFst___closed__3));
v___x_236_ = lean_string_append(v___x_234_, v___x_235_);
v___x_237_ = lean_expr_dbg_to_string(v_t_225_);
lean_dec_ref(v_t_225_);
v___x_238_ = lean_string_append(v___x_236_, v___x_237_);
lean_dec_ref(v___x_237_);
v___x_239_ = l_mkPanicMessageWithDecl(v___x_228_, v___x_229_, v___x_230_, v___x_231_, v___x_238_);
lean_dec_ref(v___x_238_);
v___x_240_ = l_panic___at___00Lean_Meta_mkPProdFst_spec__0(v___x_239_);
return v___x_240_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPProdSndM(lean_object* v_e_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_){
_start:
{
lean_object* v___x_260_; 
lean_inc(v_a_258_);
lean_inc_ref(v_a_257_);
lean_inc(v_a_256_);
lean_inc_ref(v_a_255_);
lean_inc_ref(v_e_254_);
v___x_260_ = lean_infer_type(v_e_254_, v_a_255_, v_a_256_, v_a_257_, v_a_258_);
if (lean_obj_tag(v___x_260_) == 0)
{
lean_object* v_a_261_; lean_object* v___x_262_; 
v_a_261_ = lean_ctor_get(v___x_260_, 0);
lean_inc(v_a_261_);
lean_dec_ref_known(v___x_260_, 1);
lean_inc(v_a_258_);
lean_inc_ref(v_a_257_);
lean_inc(v_a_256_);
lean_inc_ref(v_a_255_);
v___x_262_ = lean_whnf(v_a_261_, v_a_255_, v_a_256_, v_a_257_, v_a_258_);
if (lean_obj_tag(v___x_262_) == 0)
{
lean_object* v_a_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_271_; 
v_a_263_ = lean_ctor_get(v___x_262_, 0);
v_isSharedCheck_271_ = !lean_is_exclusive(v___x_262_);
if (v_isSharedCheck_271_ == 0)
{
v___x_265_ = v___x_262_;
v_isShared_266_ = v_isSharedCheck_271_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_a_263_);
lean_dec(v___x_262_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_271_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v___x_267_; lean_object* v___x_269_; 
v___x_267_ = l_Lean_Meta_mkPProdSnd(v_a_263_, v_e_254_);
if (v_isShared_266_ == 0)
{
lean_ctor_set(v___x_265_, 0, v___x_267_);
v___x_269_ = v___x_265_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v___x_267_);
v___x_269_ = v_reuseFailAlloc_270_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
return v___x_269_;
}
}
}
else
{
lean_dec_ref(v_e_254_);
return v___x_262_;
}
}
else
{
lean_dec_ref(v_e_254_);
return v___x_260_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPProdSndM___boxed(lean_object* v_e_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l_Lean_Meta_mkPProdSndM(v_e_272_, v_a_273_, v_a_274_, v_a_275_, v_a_276_);
lean_dec(v_a_276_);
lean_dec_ref(v_a_275_);
lean_dec(v_a_274_);
lean_dec_ref(v_a_273_);
return v_res_278_;
}
}
static lean_object* _init_l_Lean_Meta_PProdN_genMk___redArg___closed__3(void){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_282_ = ((lean_object*)(l_Lean_Meta_PProdN_genMk___redArg___closed__2));
v___x_283_ = lean_unsigned_to_nat(2u);
v___x_284_ = lean_unsigned_to_nat(90u);
v___x_285_ = ((lean_object*)(l_Lean_Meta_PProdN_genMk___redArg___closed__1));
v___x_286_ = ((lean_object*)(l_Lean_Meta_mkPProdFst___closed__0));
v___x_287_ = l_mkPanicMessageWithDecl(v___x_286_, v___x_285_, v___x_284_, v___x_283_, v___x_282_);
return v___x_287_;
}
}
static lean_object* _init_l_Lean_Meta_PProdN_genMk___redArg___closed__4(void){
_start:
{
lean_object* v___x_288_; 
v___x_288_ = l_instMonadEIO(lean_box(0));
return v___x_288_;
}
}
static lean_object* _init_l_Lean_Meta_PProdN_genMk___redArg___closed__5(void){
_start:
{
lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_289_ = lean_obj_once(&l_Lean_Meta_PProdN_genMk___redArg___closed__4, &l_Lean_Meta_PProdN_genMk___redArg___closed__4_once, _init_l_Lean_Meta_PProdN_genMk___redArg___closed__4);
v___x_290_ = l_StateRefT_x27_instMonad___redArg(v___x_289_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_genMk___redArg(lean_object* v_inst_295_, lean_object* v_mk_296_, lean_object* v_xs_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; uint8_t v___x_305_; uint8_t v___x_306_; 
v___x_303_ = lean_array_get_size(v_xs_297_);
v___x_304_ = lean_unsigned_to_nat(0u);
v___x_305_ = lean_nat_dec_eq(v___x_303_, v___x_304_);
v___x_306_ = lean_bool_not(v___x_305_);
if (v___x_306_ == 0)
{
lean_object* v___f_307_; lean_object* v___x_308_; lean_object* v___x_129__overap_309_; lean_object* v___x_310_; 
lean_dec_ref(v_xs_297_);
lean_dec_ref(v_mk_296_);
v___f_307_ = ((lean_object*)(l_Lean_Meta_PProdN_genMk___redArg___closed__0));
v___x_308_ = lean_obj_once(&l_Lean_Meta_PProdN_genMk___redArg___closed__3, &l_Lean_Meta_PProdN_genMk___redArg___closed__3_once, _init_l_Lean_Meta_PProdN_genMk___redArg___closed__3);
v___x_129__overap_309_ = l_panic___redArg(v___f_307_, v___x_308_);
lean_inc(v_a_301_);
lean_inc_ref(v_a_300_);
lean_inc(v_a_299_);
lean_inc_ref(v_a_298_);
v___x_310_ = lean_apply_5(v___x_129__overap_309_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, lean_box(0));
return v___x_310_;
}
else
{
lean_object* v___x_311_; lean_object* v_toApplicative_312_; lean_object* v_toFunctor_313_; lean_object* v_toSeq_314_; lean_object* v_toSeqLeft_315_; lean_object* v_toSeqRight_316_; lean_object* v___f_317_; lean_object* v___f_318_; lean_object* v___f_319_; lean_object* v___f_320_; lean_object* v___x_321_; lean_object* v___f_322_; lean_object* v___f_323_; lean_object* v___f_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v_toApplicative_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_366_; 
v___x_311_ = lean_obj_once(&l_Lean_Meta_PProdN_genMk___redArg___closed__5, &l_Lean_Meta_PProdN_genMk___redArg___closed__5_once, _init_l_Lean_Meta_PProdN_genMk___redArg___closed__5);
v_toApplicative_312_ = lean_ctor_get(v___x_311_, 0);
v_toFunctor_313_ = lean_ctor_get(v_toApplicative_312_, 0);
v_toSeq_314_ = lean_ctor_get(v_toApplicative_312_, 2);
v_toSeqLeft_315_ = lean_ctor_get(v_toApplicative_312_, 3);
v_toSeqRight_316_ = lean_ctor_get(v_toApplicative_312_, 4);
v___f_317_ = ((lean_object*)(l_Lean_Meta_PProdN_genMk___redArg___closed__6));
v___f_318_ = ((lean_object*)(l_Lean_Meta_PProdN_genMk___redArg___closed__7));
lean_inc_ref_n(v_toFunctor_313_, 2);
v___f_319_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_319_, 0, v_toFunctor_313_);
v___f_320_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_320_, 0, v_toFunctor_313_);
v___x_321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_321_, 0, v___f_319_);
lean_ctor_set(v___x_321_, 1, v___f_320_);
lean_inc(v_toSeqRight_316_);
v___f_322_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_322_, 0, v_toSeqRight_316_);
lean_inc(v_toSeqLeft_315_);
v___f_323_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_323_, 0, v_toSeqLeft_315_);
lean_inc(v_toSeq_314_);
v___f_324_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_324_, 0, v_toSeq_314_);
v___x_325_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_325_, 0, v___x_321_);
lean_ctor_set(v___x_325_, 1, v___f_317_);
lean_ctor_set(v___x_325_, 2, v___f_324_);
lean_ctor_set(v___x_325_, 3, v___f_323_);
lean_ctor_set(v___x_325_, 4, v___f_322_);
v___x_326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_326_, 0, v___x_325_);
lean_ctor_set(v___x_326_, 1, v___f_318_);
v___x_327_ = l_StateRefT_x27_instMonad___redArg(v___x_326_);
v_toApplicative_328_ = lean_ctor_get(v___x_327_, 0);
v_isSharedCheck_366_ = !lean_is_exclusive(v___x_327_);
if (v_isSharedCheck_366_ == 0)
{
lean_object* v_unused_367_; 
v_unused_367_ = lean_ctor_get(v___x_327_, 1);
lean_dec(v_unused_367_);
v___x_330_ = v___x_327_;
v_isShared_331_ = v_isSharedCheck_366_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_toApplicative_328_);
lean_dec(v___x_327_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_366_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v_toFunctor_332_; lean_object* v_toSeq_333_; lean_object* v_toSeqLeft_334_; lean_object* v_toSeqRight_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_364_; 
v_toFunctor_332_ = lean_ctor_get(v_toApplicative_328_, 0);
v_toSeq_333_ = lean_ctor_get(v_toApplicative_328_, 2);
v_toSeqLeft_334_ = lean_ctor_get(v_toApplicative_328_, 3);
v_toSeqRight_335_ = lean_ctor_get(v_toApplicative_328_, 4);
v_isSharedCheck_364_ = !lean_is_exclusive(v_toApplicative_328_);
if (v_isSharedCheck_364_ == 0)
{
lean_object* v_unused_365_; 
v_unused_365_ = lean_ctor_get(v_toApplicative_328_, 1);
lean_dec(v_unused_365_);
v___x_337_ = v_toApplicative_328_;
v_isShared_338_ = v_isSharedCheck_364_;
goto v_resetjp_336_;
}
else
{
lean_inc(v_toSeqRight_335_);
lean_inc(v_toSeqLeft_334_);
lean_inc(v_toSeq_333_);
lean_inc(v_toFunctor_332_);
lean_dec(v_toApplicative_328_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_364_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v___f_339_; lean_object* v___f_340_; lean_object* v___f_341_; lean_object* v___f_342_; lean_object* v___x_343_; lean_object* v___f_344_; lean_object* v___f_345_; lean_object* v___f_346_; lean_object* v___x_348_; 
v___f_339_ = ((lean_object*)(l_Lean_Meta_PProdN_genMk___redArg___closed__8));
v___f_340_ = ((lean_object*)(l_Lean_Meta_PProdN_genMk___redArg___closed__9));
lean_inc_ref(v_toFunctor_332_);
v___f_341_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_341_, 0, v_toFunctor_332_);
v___f_342_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_342_, 0, v_toFunctor_332_);
v___x_343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_343_, 0, v___f_341_);
lean_ctor_set(v___x_343_, 1, v___f_342_);
v___f_344_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_344_, 0, v_toSeqRight_335_);
v___f_345_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_345_, 0, v_toSeqLeft_334_);
v___f_346_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_346_, 0, v_toSeq_333_);
if (v_isShared_338_ == 0)
{
lean_ctor_set(v___x_337_, 4, v___f_344_);
lean_ctor_set(v___x_337_, 3, v___f_345_);
lean_ctor_set(v___x_337_, 2, v___f_346_);
lean_ctor_set(v___x_337_, 1, v___f_339_);
lean_ctor_set(v___x_337_, 0, v___x_343_);
v___x_348_ = v___x_337_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v___x_343_);
lean_ctor_set(v_reuseFailAlloc_363_, 1, v___f_339_);
lean_ctor_set(v_reuseFailAlloc_363_, 2, v___f_346_);
lean_ctor_set(v_reuseFailAlloc_363_, 3, v___f_345_);
lean_ctor_set(v_reuseFailAlloc_363_, 4, v___f_344_);
v___x_348_ = v_reuseFailAlloc_363_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
lean_object* v___x_350_; 
if (v_isShared_331_ == 0)
{
lean_ctor_set(v___x_330_, 1, v___f_340_);
lean_ctor_set(v___x_330_, 0, v___x_348_);
v___x_350_ = v___x_330_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v___x_348_);
lean_ctor_set(v_reuseFailAlloc_362_, 1, v___f_340_);
v___x_350_ = v_reuseFailAlloc_362_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; uint8_t v___x_356_; 
v___x_351_ = lean_unsigned_to_nat(1u);
v___x_352_ = lean_nat_sub(v___x_303_, v___x_351_);
v___x_353_ = lean_array_get(v_inst_295_, v_xs_297_, v___x_352_);
lean_dec(v___x_352_);
v___x_354_ = lean_array_pop(v_xs_297_);
v___x_355_ = lean_array_get_size(v___x_354_);
v___x_356_ = lean_nat_dec_lt(v___x_304_, v___x_355_);
if (v___x_356_ == 0)
{
lean_object* v___x_357_; 
lean_dec_ref(v___x_354_);
lean_dec_ref(v___x_350_);
lean_dec_ref(v_mk_296_);
v___x_357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_357_, 0, v___x_353_);
return v___x_357_;
}
else
{
size_t v___x_358_; size_t v___x_359_; lean_object* v___x_279__overap_360_; lean_object* v___x_361_; 
v___x_358_ = lean_usize_of_nat(v___x_355_);
v___x_359_ = ((size_t)0ULL);
v___x_279__overap_360_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_350_, v_mk_296_, v___x_354_, v___x_358_, v___x_359_, v___x_353_);
lean_inc(v_a_301_);
lean_inc_ref(v_a_300_);
lean_inc(v_a_299_);
lean_inc_ref(v_a_298_);
v___x_361_ = lean_apply_5(v___x_279__overap_360_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, lean_box(0));
return v___x_361_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_genMk___redArg___boxed(lean_object* v_inst_368_, lean_object* v_mk_369_, lean_object* v_xs_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l_Lean_Meta_PProdN_genMk___redArg(v_inst_368_, v_mk_369_, v_xs_370_, v_a_371_, v_a_372_, v_a_373_, v_a_374_);
lean_dec(v_a_374_);
lean_dec_ref(v_a_373_);
lean_dec(v_a_372_);
lean_dec_ref(v_a_371_);
lean_dec(v_inst_368_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_genMk(lean_object* v_00_u03b1_377_, lean_object* v_inst_378_, lean_object* v_mk_379_, lean_object* v_xs_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = l_Lean_Meta_PProdN_genMk___redArg(v_inst_378_, v_mk_379_, v_xs_380_, v_a_381_, v_a_382_, v_a_383_, v_a_384_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_genMk___boxed(lean_object* v_00_u03b1_387_, lean_object* v_inst_388_, lean_object* v_mk_389_, lean_object* v_xs_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_Lean_Meta_PProdN_genMk(v_00_u03b1_387_, v_inst_388_, v_mk_389_, v_xs_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_);
lean_dec(v_a_394_);
lean_dec_ref(v_a_393_);
lean_dec(v_a_392_);
lean_dec_ref(v_a_391_);
lean_dec(v_inst_388_);
return v_res_396_;
}
}
static lean_object* _init_l_Lean_Meta_PProdN_pack___closed__5(void){
_start:
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_404_ = lean_box(0);
v___x_405_ = ((lean_object*)(l_Lean_Meta_PProdN_pack___closed__4));
v___x_406_ = l_Lean_Expr_const___override(v___x_405_, v___x_404_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_pack(lean_object* v_lvl_407_, lean_object* v_xs_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_){
_start:
{
lean_object* v___x_414_; lean_object* v___x_415_; uint8_t v___x_416_; 
v___x_414_ = lean_array_get_size(v_xs_408_);
v___x_415_ = lean_unsigned_to_nat(0u);
v___x_416_ = lean_nat_dec_eq(v___x_414_, v___x_415_);
if (v___x_416_ == 0)
{
lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
lean_dec(v_lvl_407_);
v___x_417_ = l_Lean_instInhabitedExpr;
v___x_418_ = ((lean_object*)(l_Lean_Meta_PProdN_pack___closed__0));
v___x_419_ = l_Lean_Meta_PProdN_genMk___redArg(v___x_417_, v___x_418_, v_xs_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_);
return v___x_419_;
}
else
{
uint8_t v___x_420_; 
lean_dec_ref(v_xs_408_);
v___x_420_ = l_Lean_Level_isAlwaysZero(v_lvl_407_);
if (v___x_420_ == 0)
{
lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_421_ = ((lean_object*)(l_Lean_Meta_PProdN_pack___closed__2));
v___x_422_ = lean_box(0);
v___x_423_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_423_, 0, v_lvl_407_);
lean_ctor_set(v___x_423_, 1, v___x_422_);
v___x_424_ = l_Lean_Expr_const___override(v___x_421_, v___x_423_);
v___x_425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_425_, 0, v___x_424_);
return v___x_425_;
}
else
{
lean_object* v___x_426_; lean_object* v___x_427_; 
lean_dec(v_lvl_407_);
v___x_426_ = lean_obj_once(&l_Lean_Meta_PProdN_pack___closed__5, &l_Lean_Meta_PProdN_pack___closed__5_once, _init_l_Lean_Meta_PProdN_pack___closed__5);
v___x_427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_427_, 0, v___x_426_);
return v___x_427_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_pack___boxed(lean_object* v_lvl_428_, lean_object* v_xs_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l_Lean_Meta_PProdN_pack(v_lvl_428_, v_xs_429_, v_a_430_, v_a_431_, v_a_432_, v_a_433_);
lean_dec(v_a_433_);
lean_dec_ref(v_a_432_);
lean_dec(v_a_431_);
lean_dec_ref(v_a_430_);
return v_res_435_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_unpack_go___redArg(lean_object* v_e_436_, lean_object* v_remaining_437_, lean_object* v_acc_438_){
_start:
{
lean_object* v___x_443_; uint8_t v___x_444_; 
v___x_443_ = lean_unsigned_to_nat(0u);
v___x_444_ = lean_nat_dec_eq(v_remaining_437_, v___x_443_);
if (v___x_444_ == 0)
{
if (lean_obj_tag(v_e_436_) == 5)
{
lean_object* v_fn_445_; 
v_fn_445_ = lean_ctor_get(v_e_436_, 0);
if (lean_obj_tag(v_fn_445_) == 5)
{
lean_object* v_fn_446_; 
v_fn_446_ = lean_ctor_get(v_fn_445_, 0);
if (lean_obj_tag(v_fn_446_) == 4)
{
lean_object* v_declName_447_; 
v_declName_447_ = lean_ctor_get(v_fn_446_, 0);
if (lean_obj_tag(v_declName_447_) == 1)
{
lean_object* v_pre_448_; 
v_pre_448_ = lean_ctor_get(v_declName_447_, 0);
if (lean_obj_tag(v_pre_448_) == 0)
{
lean_object* v_arg_449_; lean_object* v_arg_450_; lean_object* v_str_451_; lean_object* v___x_452_; uint8_t v___x_453_; 
v_arg_449_ = lean_ctor_get(v_e_436_, 1);
v_arg_450_ = lean_ctor_get(v_fn_445_, 1);
v_str_451_ = lean_ctor_get(v_declName_447_, 1);
v___x_452_ = ((lean_object*)(l_Lean_Meta_mkPProd___closed__0));
v___x_453_ = lean_string_dec_eq(v_str_451_, v___x_452_);
if (v___x_453_ == 0)
{
lean_dec(v_remaining_437_);
goto v___jp_440_;
}
else
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
lean_inc_ref(v_arg_450_);
lean_inc_ref(v_arg_449_);
lean_dec_ref_known(v_e_436_, 2);
v___x_454_ = lean_unsigned_to_nat(1u);
v___x_455_ = lean_nat_sub(v_remaining_437_, v___x_454_);
lean_dec(v_remaining_437_);
v___x_456_ = lean_array_push(v_acc_438_, v_arg_450_);
v_e_436_ = v_arg_449_;
v_remaining_437_ = v___x_455_;
v_acc_438_ = v___x_456_;
goto _start;
}
}
else
{
lean_dec(v_remaining_437_);
goto v___jp_440_;
}
}
else
{
lean_dec(v_remaining_437_);
goto v___jp_440_;
}
}
else
{
lean_dec(v_remaining_437_);
goto v___jp_440_;
}
}
else
{
lean_dec(v_remaining_437_);
goto v___jp_440_;
}
}
else
{
lean_dec(v_remaining_437_);
goto v___jp_440_;
}
}
else
{
lean_object* v___x_458_; 
lean_dec(v_remaining_437_);
lean_dec_ref(v_e_436_);
v___x_458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_458_, 0, v_acc_438_);
return v___x_458_;
}
v___jp_440_:
{
lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_441_ = lean_array_push(v_acc_438_, v_e_436_);
v___x_442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_442_, 0, v___x_441_);
return v___x_442_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_unpack_go___redArg___boxed(lean_object* v_e_459_, lean_object* v_remaining_460_, lean_object* v_acc_461_, lean_object* v_a_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_unpack_go___redArg(v_e_459_, v_remaining_460_, v_acc_461_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_unpack_go(lean_object* v_e_464_, lean_object* v_remaining_465_, lean_object* v_acc_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_){
_start:
{
lean_object* v___x_472_; 
v___x_472_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_unpack_go___redArg(v_e_464_, v_remaining_465_, v_acc_466_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_unpack_go___boxed(lean_object* v_e_473_, lean_object* v_remaining_474_, lean_object* v_acc_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_unpack_go(v_e_473_, v_remaining_474_, v_acc_475_, v_a_476_, v_a_477_, v_a_478_, v_a_479_);
lean_dec(v_a_479_);
lean_dec_ref(v_a_478_);
lean_dec(v_a_477_);
lean_dec_ref(v_a_476_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_unpack___redArg(lean_object* v_e_484_, lean_object* v_n_485_){
_start:
{
if (lean_obj_tag(v_e_484_) == 4)
{
lean_object* v_declName_493_; 
v_declName_493_ = lean_ctor_get(v_e_484_, 0);
if (lean_obj_tag(v_declName_493_) == 1)
{
lean_object* v_pre_494_; 
v_pre_494_ = lean_ctor_get(v_declName_493_, 0);
if (lean_obj_tag(v_pre_494_) == 0)
{
lean_object* v_str_495_; lean_object* v___x_496_; uint8_t v___x_497_; 
v_str_495_ = lean_ctor_get(v_declName_493_, 1);
v___x_496_ = ((lean_object*)(l_Lean_Meta_PProdN_pack___closed__3));
v___x_497_ = lean_string_dec_eq(v_str_495_, v___x_496_);
if (v___x_497_ == 0)
{
lean_object* v___x_498_; uint8_t v___x_499_; 
v___x_498_ = ((lean_object*)(l_Lean_Meta_PProdN_pack___closed__1));
v___x_499_ = lean_string_dec_eq(v_str_495_, v___x_498_);
if (v___x_499_ == 0)
{
goto v___jp_487_;
}
else
{
lean_dec_ref_known(v_e_484_, 2);
lean_dec(v_n_485_);
goto v___jp_490_;
}
}
else
{
lean_dec_ref_known(v_e_484_, 2);
lean_dec(v_n_485_);
goto v___jp_490_;
}
}
else
{
goto v___jp_487_;
}
}
else
{
goto v___jp_487_;
}
}
else
{
goto v___jp_487_;
}
v___jp_487_:
{
lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_488_ = ((lean_object*)(l_Lean_Meta_PProdN_unpack___redArg___closed__0));
v___x_489_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_unpack_go___redArg(v_e_484_, v_n_485_, v___x_488_);
return v___x_489_;
}
v___jp_490_:
{
lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_491_ = ((lean_object*)(l_Lean_Meta_PProdN_unpack___redArg___closed__0));
v___x_492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_492_, 0, v___x_491_);
return v___x_492_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_unpack___redArg___boxed(lean_object* v_e_500_, lean_object* v_n_501_, lean_object* v_a_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l_Lean_Meta_PProdN_unpack___redArg(v_e_500_, v_n_501_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_unpack(lean_object* v_e_504_, lean_object* v_n_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_){
_start:
{
lean_object* v___x_511_; 
v___x_511_ = l_Lean_Meta_PProdN_unpack___redArg(v_e_504_, v_n_505_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_unpack___boxed(lean_object* v_e_512_, lean_object* v_n_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l_Lean_Meta_PProdN_unpack(v_e_512_, v_n_513_, v_a_514_, v_a_515_, v_a_516_, v_a_517_);
lean_dec(v_a_517_);
lean_dec_ref(v_a_516_);
lean_dec(v_a_515_);
lean_dec_ref(v_a_514_);
return v_res_519_;
}
}
static lean_object* _init_l_Lean_Meta_PProdN_mk___closed__4(void){
_start:
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_528_ = lean_box(0);
v___x_529_ = ((lean_object*)(l_Lean_Meta_PProdN_mk___closed__3));
v___x_530_ = l_Lean_Expr_const___override(v___x_529_, v___x_528_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_mk(lean_object* v_lvl_531_, lean_object* v_xs_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; uint8_t v___x_540_; 
v___x_538_ = lean_array_get_size(v_xs_532_);
v___x_539_ = lean_unsigned_to_nat(0u);
v___x_540_ = lean_nat_dec_eq(v___x_538_, v___x_539_);
if (v___x_540_ == 0)
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
lean_dec(v_lvl_531_);
v___x_541_ = l_Lean_instInhabitedExpr;
v___x_542_ = ((lean_object*)(l_Lean_Meta_PProdN_mk___closed__0));
v___x_543_ = l_Lean_Meta_PProdN_genMk___redArg(v___x_541_, v___x_542_, v_xs_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_);
return v___x_543_;
}
else
{
uint8_t v___x_544_; 
lean_dec_ref(v_xs_532_);
v___x_544_ = l_Lean_Level_isAlwaysZero(v_lvl_531_);
if (v___x_544_ == 0)
{
lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_545_ = ((lean_object*)(l_Lean_Meta_PProdN_mk___closed__2));
v___x_546_ = lean_box(0);
v___x_547_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_547_, 0, v_lvl_531_);
lean_ctor_set(v___x_547_, 1, v___x_546_);
v___x_548_ = l_Lean_Expr_const___override(v___x_545_, v___x_547_);
v___x_549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_549_, 0, v___x_548_);
return v___x_549_;
}
else
{
lean_object* v___x_550_; lean_object* v___x_551_; 
lean_dec(v_lvl_531_);
v___x_550_ = lean_obj_once(&l_Lean_Meta_PProdN_mk___closed__4, &l_Lean_Meta_PProdN_mk___closed__4_once, _init_l_Lean_Meta_PProdN_mk___closed__4);
v___x_551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_551_, 0, v___x_550_);
return v___x_551_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_mk___boxed(lean_object* v_lvl_552_, lean_object* v_xs_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_Lean_Meta_PProdN_mk(v_lvl_552_, v_xs_553_, v_a_554_, v_a_555_, v_a_556_, v_a_557_);
lean_dec(v_a_557_);
lean_dec_ref(v_a_556_);
lean_dec(v_a_555_);
lean_dec_ref(v_a_554_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_proj_spec__0___redArg(lean_object* v_upperBound_560_, lean_object* v_a_561_, lean_object* v_b_562_){
_start:
{
uint8_t v___x_563_; 
v___x_563_ = lean_nat_dec_lt(v_a_561_, v_upperBound_560_);
if (v___x_563_ == 0)
{
lean_dec(v_a_561_);
return v_b_562_;
}
else
{
lean_object* v_fst_564_; lean_object* v_snd_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_577_; 
v_fst_564_ = lean_ctor_get(v_b_562_, 0);
v_snd_565_ = lean_ctor_get(v_b_562_, 1);
v_isSharedCheck_577_ = !lean_is_exclusive(v_b_562_);
if (v_isSharedCheck_577_ == 0)
{
v___x_567_ = v_b_562_;
v_isShared_568_ = v_isSharedCheck_577_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_snd_565_);
lean_inc(v_fst_564_);
lean_dec(v_b_562_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_577_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_572_; 
lean_inc(v_fst_564_);
v___x_569_ = l_Lean_Meta_mkPProdSnd(v_fst_564_, v_snd_565_);
v___x_570_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_mkTypeSnd(v_fst_564_);
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 1, v___x_569_);
lean_ctor_set(v___x_567_, 0, v___x_570_);
v___x_572_ = v___x_567_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v___x_570_);
lean_ctor_set(v_reuseFailAlloc_576_, 1, v___x_569_);
v___x_572_ = v_reuseFailAlloc_576_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_573_ = lean_unsigned_to_nat(1u);
v___x_574_ = lean_nat_add(v_a_561_, v___x_573_);
lean_dec(v_a_561_);
v_a_561_ = v___x_574_;
v_b_562_ = v___x_572_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_proj_spec__0___redArg___boxed(lean_object* v_upperBound_578_, lean_object* v_a_579_, lean_object* v_b_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_proj_spec__0___redArg(v_upperBound_578_, v_a_579_, v_b_580_);
lean_dec(v_upperBound_578_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_proj(lean_object* v_n_582_, lean_object* v_i_583_, lean_object* v_t_584_, lean_object* v_e_585_){
_start:
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v_fst_589_; lean_object* v_snd_590_; lean_object* v___x_591_; lean_object* v___x_592_; uint8_t v___x_593_; 
v___x_586_ = lean_unsigned_to_nat(0u);
v___x_587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_587_, 0, v_t_584_);
lean_ctor_set(v___x_587_, 1, v_e_585_);
v___x_588_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_proj_spec__0___redArg(v_i_583_, v___x_586_, v___x_587_);
v_fst_589_ = lean_ctor_get(v___x_588_, 0);
lean_inc(v_fst_589_);
v_snd_590_ = lean_ctor_get(v___x_588_, 1);
lean_inc(v_snd_590_);
lean_dec_ref(v___x_588_);
v___x_591_ = lean_unsigned_to_nat(1u);
v___x_592_ = lean_nat_add(v_i_583_, v___x_591_);
v___x_593_ = lean_nat_dec_lt(v___x_592_, v_n_582_);
lean_dec(v___x_592_);
if (v___x_593_ == 0)
{
lean_dec(v_fst_589_);
return v_snd_590_;
}
else
{
lean_object* v___x_594_; 
v___x_594_ = l_Lean_Meta_mkPProdFst(v_fst_589_, v_snd_590_);
return v___x_594_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_proj___boxed(lean_object* v_n_595_, lean_object* v_i_596_, lean_object* v_t_597_, lean_object* v_e_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l_Lean_Meta_PProdN_proj(v_n_595_, v_i_596_, v_t_597_, v_e_598_);
lean_dec(v_i_596_);
lean_dec(v_n_595_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_proj_spec__0(lean_object* v_upperBound_600_, lean_object* v_inst_601_, lean_object* v_R_602_, lean_object* v_a_603_, lean_object* v_b_604_, lean_object* v_c_605_){
_start:
{
lean_object* v___x_606_; 
v___x_606_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_proj_spec__0___redArg(v_upperBound_600_, v_a_603_, v_b_604_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_proj_spec__0___boxed(lean_object* v_upperBound_607_, lean_object* v_inst_608_, lean_object* v_R_609_, lean_object* v_a_610_, lean_object* v_b_611_, lean_object* v_c_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_proj_spec__0(v_upperBound_607_, v_inst_608_, v_R_609_, v_a_610_, v_b_611_, v_c_612_);
lean_dec(v_upperBound_607_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_projs___lam__0(lean_object* v_n_614_, lean_object* v_t_615_, lean_object* v_e_616_, lean_object* v_i_617_){
_start:
{
lean_object* v___x_618_; 
v___x_618_ = l_Lean_Meta_PProdN_proj(v_n_614_, v_i_617_, v_t_615_, v_e_616_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_projs___lam__0___boxed(lean_object* v_n_619_, lean_object* v_t_620_, lean_object* v_e_621_, lean_object* v_i_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l_Lean_Meta_PProdN_projs___lam__0(v_n_619_, v_t_620_, v_e_621_, v_i_622_);
lean_dec(v_i_622_);
lean_dec(v_n_619_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_projs(lean_object* v_n_624_, lean_object* v_t_625_, lean_object* v_e_626_){
_start:
{
lean_object* v___f_627_; lean_object* v___x_628_; 
lean_inc(v_n_624_);
v___f_627_ = lean_alloc_closure((void*)(l_Lean_Meta_PProdN_projs___lam__0___boxed), 4, 3);
lean_closure_set(v___f_627_, 0, v_n_624_);
lean_closure_set(v___f_627_, 1, v_t_625_);
lean_closure_set(v___f_627_, 2, v_e_626_);
v___x_628_ = l_Array_ofFn___redArg(v_n_624_, v___f_627_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_projM_spec__0___redArg(lean_object* v_upperBound_629_, lean_object* v_a_630_, lean_object* v_b_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_){
_start:
{
uint8_t v___x_637_; 
v___x_637_ = lean_nat_dec_lt(v_a_630_, v_upperBound_629_);
if (v___x_637_ == 0)
{
lean_object* v___x_638_; 
lean_dec(v_a_630_);
v___x_638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_638_, 0, v_b_631_);
return v___x_638_;
}
else
{
lean_object* v___x_639_; 
v___x_639_ = l_Lean_Meta_mkPProdSndM(v_b_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_object* v_a_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v_a_640_ = lean_ctor_get(v___x_639_, 0);
lean_inc(v_a_640_);
lean_dec_ref_known(v___x_639_, 1);
v___x_641_ = lean_unsigned_to_nat(1u);
v___x_642_ = lean_nat_add(v_a_630_, v___x_641_);
lean_dec(v_a_630_);
v_a_630_ = v___x_642_;
v_b_631_ = v_a_640_;
goto _start;
}
else
{
lean_dec(v_a_630_);
return v___x_639_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_projM_spec__0___redArg___boxed(lean_object* v_upperBound_644_, lean_object* v_a_645_, lean_object* v_b_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_){
_start:
{
lean_object* v_res_652_; 
v_res_652_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_projM_spec__0___redArg(v_upperBound_644_, v_a_645_, v_b_646_, v___y_647_, v___y_648_, v___y_649_, v___y_650_);
lean_dec(v___y_650_);
lean_dec_ref(v___y_649_);
lean_dec(v___y_648_);
lean_dec_ref(v___y_647_);
lean_dec(v_upperBound_644_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_projM(lean_object* v_n_653_, lean_object* v_i_654_, lean_object* v_e_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_){
_start:
{
lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_661_ = lean_unsigned_to_nat(0u);
v___x_662_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_projM_spec__0___redArg(v_i_654_, v___x_661_, v_e_655_, v_a_656_, v_a_657_, v_a_658_, v_a_659_);
if (lean_obj_tag(v___x_662_) == 0)
{
lean_object* v_a_663_; lean_object* v___x_664_; lean_object* v___x_665_; uint8_t v___x_666_; 
v_a_663_ = lean_ctor_get(v___x_662_, 0);
lean_inc(v_a_663_);
v___x_664_ = lean_unsigned_to_nat(1u);
v___x_665_ = lean_nat_add(v_i_654_, v___x_664_);
v___x_666_ = lean_nat_dec_lt(v___x_665_, v_n_653_);
lean_dec(v___x_665_);
if (v___x_666_ == 0)
{
lean_dec(v_a_663_);
return v___x_662_;
}
else
{
lean_object* v___x_667_; 
lean_dec_ref_known(v___x_662_, 1);
v___x_667_ = l_Lean_Meta_mkPProdFstM(v_a_663_, v_a_656_, v_a_657_, v_a_658_, v_a_659_);
return v___x_667_;
}
}
else
{
return v___x_662_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_projM___boxed(lean_object* v_n_668_, lean_object* v_i_669_, lean_object* v_e_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l_Lean_Meta_PProdN_projM(v_n_668_, v_i_669_, v_e_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_);
lean_dec(v_a_674_);
lean_dec_ref(v_a_673_);
lean_dec(v_a_672_);
lean_dec_ref(v_a_671_);
lean_dec(v_i_669_);
lean_dec(v_n_668_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_projM_spec__0(lean_object* v_upperBound_677_, lean_object* v_inst_678_, lean_object* v_R_679_, lean_object* v_a_680_, lean_object* v_b_681_, lean_object* v_c_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_){
_start:
{
lean_object* v___x_688_; 
v___x_688_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_projM_spec__0___redArg(v_upperBound_677_, v_a_680_, v_b_681_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_projM_spec__0___boxed(lean_object* v_upperBound_689_, lean_object* v_inst_690_, lean_object* v_R_691_, lean_object* v_a_692_, lean_object* v_b_693_, lean_object* v_c_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_projM_spec__0(v_upperBound_689_, v_inst_690_, v_R_691_, v_a_692_, v_b_693_, v_c_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_);
lean_dec(v___y_698_);
lean_dec_ref(v___y_697_);
lean_dec(v___y_696_);
lean_dec_ref(v___y_695_);
lean_dec(v_upperBound_689_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_PProdN_packLambdas_spec__0(lean_object* v_msg_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_){
_start:
{
lean_object* v___f_707_; lean_object* v___x_407__overap_708_; lean_object* v___x_709_; 
v___f_707_ = ((lean_object*)(l_Lean_Meta_PProdN_genMk___redArg___closed__0));
v___x_407__overap_708_ = lean_panic_fn_borrowed(v___f_707_, v_msg_701_);
lean_inc(v___y_705_);
lean_inc_ref(v___y_704_);
lean_inc(v___y_703_);
lean_inc_ref(v___y_702_);
v___x_709_ = lean_apply_5(v___x_407__overap_708_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, lean_box(0));
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_PProdN_packLambdas_spec__0___boxed(lean_object* v_msg_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_){
_start:
{
lean_object* v_res_716_; 
v_res_716_ = l_panic___at___00Lean_Meta_PProdN_packLambdas_spec__0(v_msg_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_);
lean_dec(v___y_714_);
lean_dec_ref(v___y_713_);
lean_dec(v___y_712_);
lean_dec_ref(v___y_711_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___redArg___lam__0(lean_object* v_k_717_, lean_object* v_b_718_, lean_object* v_c_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_){
_start:
{
lean_object* v___x_725_; 
lean_inc(v___y_723_);
lean_inc_ref(v___y_722_);
lean_inc(v___y_721_);
lean_inc_ref(v___y_720_);
v___x_725_ = lean_apply_7(v_k_717_, v_b_718_, v_c_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, lean_box(0));
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___redArg___lam__0___boxed(lean_object* v_k_726_, lean_object* v_b_727_, lean_object* v_c_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___redArg___lam__0(v_k_726_, v_b_727_, v_c_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___redArg(lean_object* v_type_735_, lean_object* v_k_736_, uint8_t v_cleanupAnnotations_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_){
_start:
{
lean_object* v___f_743_; uint8_t v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
v___f_743_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_743_, 0, v_k_736_);
v___x_744_ = 0;
v___x_745_ = lean_box(0);
v___x_746_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_744_, v___x_745_, v_type_735_, v___f_743_, v_cleanupAnnotations_737_, v___x_744_, v___y_738_, v___y_739_, v___y_740_, v___y_741_);
if (lean_obj_tag(v___x_746_) == 0)
{
lean_object* v_a_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_754_; 
v_a_747_ = lean_ctor_get(v___x_746_, 0);
v_isSharedCheck_754_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_754_ == 0)
{
v___x_749_ = v___x_746_;
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_a_747_);
lean_dec(v___x_746_);
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
v_reuseFailAlloc_753_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_762_; 
v_a_755_ = lean_ctor_get(v___x_746_, 0);
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_762_ == 0)
{
v___x_757_ = v___x_746_;
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_a_755_);
lean_dec(v___x_746_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___redArg___boxed(lean_object* v_type_763_, lean_object* v_k_764_, lean_object* v_cleanupAnnotations_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_771_; lean_object* v_res_772_; 
v_cleanupAnnotations_boxed_771_ = lean_unbox(v_cleanupAnnotations_765_);
v_res_772_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___redArg(v_type_763_, v_k_764_, v_cleanupAnnotations_boxed_771_, v___y_766_, v___y_767_, v___y_768_, v___y_769_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
lean_dec(v___y_767_);
lean_dec_ref(v___y_766_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2(lean_object* v_00_u03b1_773_, lean_object* v_type_774_, lean_object* v_k_775_, uint8_t v_cleanupAnnotations_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_){
_start:
{
lean_object* v___x_782_; 
v___x_782_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___redArg(v_type_774_, v_k_775_, v_cleanupAnnotations_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_);
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___boxed(lean_object* v_00_u03b1_783_, lean_object* v_type_784_, lean_object* v_k_785_, lean_object* v_cleanupAnnotations_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_792_; lean_object* v_res_793_; 
v_cleanupAnnotations_boxed_792_ = lean_unbox(v_cleanupAnnotations_786_);
v_res_793_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2(v_00_u03b1_783_, v_type_784_, v_k_785_, v_cleanupAnnotations_boxed_792_, v___y_787_, v___y_788_, v___y_789_, v___y_790_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
lean_dec(v___y_788_);
lean_dec_ref(v___y_787_);
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_PProdN_packLambdas_spec__1(lean_object* v_xs_794_, size_t v_sz_795_, size_t v_i_796_, lean_object* v_bs_797_){
_start:
{
uint8_t v___x_798_; 
v___x_798_ = lean_usize_dec_lt(v_i_796_, v_sz_795_);
if (v___x_798_ == 0)
{
lean_dec_ref(v_xs_794_);
return v_bs_797_;
}
else
{
lean_object* v_v_799_; lean_object* v___x_800_; lean_object* v_bs_x27_801_; lean_object* v___x_802_; size_t v___x_803_; size_t v___x_804_; lean_object* v___x_805_; 
v_v_799_ = lean_array_uget(v_bs_797_, v_i_796_);
v___x_800_ = lean_unsigned_to_nat(0u);
v_bs_x27_801_ = lean_array_uset(v_bs_797_, v_i_796_, v___x_800_);
lean_inc_ref(v_xs_794_);
v___x_802_ = l_Lean_Expr_beta(v_v_799_, v_xs_794_);
v___x_803_ = ((size_t)1ULL);
v___x_804_ = lean_usize_add(v_i_796_, v___x_803_);
v___x_805_ = lean_array_uset(v_bs_x27_801_, v_i_796_, v___x_802_);
v_i_796_ = v___x_804_;
v_bs_797_ = v___x_805_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_PProdN_packLambdas_spec__1___boxed(lean_object* v_xs_807_, lean_object* v_sz_808_, lean_object* v_i_809_, lean_object* v_bs_810_){
_start:
{
size_t v_sz_boxed_811_; size_t v_i_boxed_812_; lean_object* v_res_813_; 
v_sz_boxed_811_ = lean_unbox_usize(v_sz_808_);
lean_dec(v_sz_808_);
v_i_boxed_812_ = lean_unbox_usize(v_i_809_);
lean_dec(v_i_809_);
v_res_813_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_PProdN_packLambdas_spec__1(v_xs_807_, v_sz_boxed_811_, v_i_boxed_812_, v_bs_810_);
return v_res_813_;
}
}
static lean_object* _init_l_Lean_Meta_PProdN_packLambdas___lam__0___closed__2(void){
_start:
{
lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_816_ = ((lean_object*)(l_Lean_Meta_PProdN_packLambdas___lam__0___closed__1));
v___x_817_ = lean_unsigned_to_nat(4u);
v___x_818_ = lean_unsigned_to_nat(175u);
v___x_819_ = ((lean_object*)(l_Lean_Meta_PProdN_packLambdas___lam__0___closed__0));
v___x_820_ = ((lean_object*)(l_Lean_Meta_mkPProdFst___closed__0));
v___x_821_ = l_mkPanicMessageWithDecl(v___x_820_, v___x_819_, v___x_818_, v___x_817_, v___x_816_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_packLambdas___lam__0(lean_object* v_es_822_, uint8_t v___x_823_, lean_object* v_xs_824_, lean_object* v_sort_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_){
_start:
{
uint8_t v___x_831_; 
v___x_831_ = l_Lean_Expr_isSort(v_sort_825_);
if (v___x_831_ == 0)
{
lean_object* v___x_832_; lean_object* v___x_833_; 
lean_dec_ref(v_xs_824_);
lean_dec_ref(v_es_822_);
v___x_832_ = lean_obj_once(&l_Lean_Meta_PProdN_packLambdas___lam__0___closed__2, &l_Lean_Meta_PProdN_packLambdas___lam__0___closed__2_once, _init_l_Lean_Meta_PProdN_packLambdas___lam__0___closed__2);
v___x_833_ = l_panic___at___00Lean_Meta_PProdN_packLambdas_spec__0(v___x_832_, v___y_826_, v___y_827_, v___y_828_, v___y_829_);
return v___x_833_;
}
else
{
size_t v_sz_834_; size_t v___x_835_; lean_object* v_es_x27_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
v_sz_834_ = lean_array_size(v_es_822_);
v___x_835_ = ((size_t)0ULL);
lean_inc_ref(v_xs_824_);
v_es_x27_836_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_PProdN_packLambdas_spec__1(v_xs_824_, v_sz_834_, v___x_835_, v_es_822_);
v___x_837_ = l_Lean_Expr_sortLevel_x21(v_sort_825_);
v___x_838_ = l_Lean_Meta_PProdN_pack(v___x_837_, v_es_x27_836_, v___y_826_, v___y_827_, v___y_828_, v___y_829_);
if (lean_obj_tag(v___x_838_) == 0)
{
lean_object* v_a_839_; uint8_t v___x_840_; lean_object* v___x_841_; 
v_a_839_ = lean_ctor_get(v___x_838_, 0);
lean_inc(v_a_839_);
lean_dec_ref_known(v___x_838_, 1);
v___x_840_ = 1;
v___x_841_ = l_Lean_Meta_mkLambdaFVars(v_xs_824_, v_a_839_, v___x_823_, v___x_831_, v___x_823_, v___x_831_, v___x_840_, v___y_826_, v___y_827_, v___y_828_, v___y_829_);
lean_dec_ref(v_xs_824_);
return v___x_841_;
}
else
{
lean_dec_ref(v_xs_824_);
return v___x_838_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_packLambdas___lam__0___boxed(lean_object* v_es_842_, lean_object* v___x_843_, lean_object* v_xs_844_, lean_object* v_sort_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_){
_start:
{
uint8_t v___x_1006__boxed_851_; lean_object* v_res_852_; 
v___x_1006__boxed_851_ = lean_unbox(v___x_843_);
v_res_852_ = l_Lean_Meta_PProdN_packLambdas___lam__0(v_es_842_, v___x_1006__boxed_851_, v_xs_844_, v_sort_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_);
lean_dec(v___y_849_);
lean_dec_ref(v___y_848_);
lean_dec(v___y_847_);
lean_dec_ref(v___y_846_);
lean_dec_ref(v_sort_845_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_packLambdas(lean_object* v_type_853_, lean_object* v_es_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_){
_start:
{
lean_object* v___x_860_; lean_object* v___x_861_; uint8_t v___x_862_; 
v___x_860_ = lean_array_get_size(v_es_854_);
v___x_861_ = lean_unsigned_to_nat(1u);
v___x_862_ = lean_nat_dec_eq(v___x_860_, v___x_861_);
if (v___x_862_ == 0)
{
lean_object* v___x_863_; lean_object* v___f_864_; lean_object* v___x_865_; 
v___x_863_ = lean_box(v___x_862_);
v___f_864_ = lean_alloc_closure((void*)(l_Lean_Meta_PProdN_packLambdas___lam__0___boxed), 9, 2);
lean_closure_set(v___f_864_, 0, v_es_854_);
lean_closure_set(v___f_864_, 1, v___x_863_);
v___x_865_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___redArg(v_type_853_, v___f_864_, v___x_862_, v_a_855_, v_a_856_, v_a_857_, v_a_858_);
return v___x_865_;
}
else
{
lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; 
lean_dec_ref(v_type_853_);
v___x_866_ = lean_unsigned_to_nat(0u);
v___x_867_ = lean_array_fget(v_es_854_, v___x_866_);
lean_dec_ref(v_es_854_);
v___x_868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_868_, 0, v___x_867_);
return v___x_868_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_packLambdas___boxed(lean_object* v_type_869_, lean_object* v_es_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l_Lean_Meta_PProdN_packLambdas(v_type_869_, v_es_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_);
lean_dec(v_a_874_);
lean_dec_ref(v_a_873_);
lean_dec(v_a_872_);
lean_dec_ref(v_a_871_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_mkLambdas___lam__0(lean_object* v_es_877_, uint8_t v___x_878_, lean_object* v_xs_879_, lean_object* v_body_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_){
_start:
{
lean_object* v___x_886_; 
v___x_886_ = l_Lean_Meta_getLevel(v_body_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_);
if (lean_obj_tag(v___x_886_) == 0)
{
lean_object* v_a_887_; size_t v_sz_888_; size_t v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v_a_887_ = lean_ctor_get(v___x_886_, 0);
lean_inc(v_a_887_);
lean_dec_ref_known(v___x_886_, 1);
v_sz_888_ = lean_array_size(v_es_877_);
v___x_889_ = ((size_t)0ULL);
lean_inc_ref(v_xs_879_);
v___x_890_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_PProdN_packLambdas_spec__1(v_xs_879_, v_sz_888_, v___x_889_, v_es_877_);
v___x_891_ = l_Lean_Meta_PProdN_mk(v_a_887_, v___x_890_, v___y_881_, v___y_882_, v___y_883_, v___y_884_);
if (lean_obj_tag(v___x_891_) == 0)
{
lean_object* v_a_892_; uint8_t v___x_893_; uint8_t v___x_894_; lean_object* v___x_895_; 
v_a_892_ = lean_ctor_get(v___x_891_, 0);
lean_inc(v_a_892_);
lean_dec_ref_known(v___x_891_, 1);
v___x_893_ = 1;
v___x_894_ = 1;
v___x_895_ = l_Lean_Meta_mkLambdaFVars(v_xs_879_, v_a_892_, v___x_878_, v___x_893_, v___x_878_, v___x_893_, v___x_894_, v___y_881_, v___y_882_, v___y_883_, v___y_884_);
lean_dec_ref(v_xs_879_);
return v___x_895_;
}
else
{
lean_dec_ref(v_xs_879_);
return v___x_891_;
}
}
else
{
lean_object* v_a_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_903_; 
lean_dec_ref(v_xs_879_);
lean_dec_ref(v_es_877_);
v_a_896_ = lean_ctor_get(v___x_886_, 0);
v_isSharedCheck_903_ = !lean_is_exclusive(v___x_886_);
if (v_isSharedCheck_903_ == 0)
{
v___x_898_ = v___x_886_;
v_isShared_899_ = v_isSharedCheck_903_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_a_896_);
lean_dec(v___x_886_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_903_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v___x_901_; 
if (v_isShared_899_ == 0)
{
v___x_901_ = v___x_898_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_a_896_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_mkLambdas___lam__0___boxed(lean_object* v_es_904_, lean_object* v___x_905_, lean_object* v_xs_906_, lean_object* v_body_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_){
_start:
{
uint8_t v___x_371__boxed_913_; lean_object* v_res_914_; 
v___x_371__boxed_913_ = lean_unbox(v___x_905_);
v_res_914_ = l_Lean_Meta_PProdN_mkLambdas___lam__0(v_es_904_, v___x_371__boxed_913_, v_xs_906_, v_body_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_);
lean_dec(v___y_911_);
lean_dec_ref(v___y_910_);
lean_dec(v___y_909_);
lean_dec_ref(v___y_908_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_mkLambdas(lean_object* v_type_915_, lean_object* v_es_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_){
_start:
{
lean_object* v___x_922_; lean_object* v___x_923_; uint8_t v___x_924_; 
v___x_922_ = lean_array_get_size(v_es_916_);
v___x_923_ = lean_unsigned_to_nat(1u);
v___x_924_ = lean_nat_dec_eq(v___x_922_, v___x_923_);
if (v___x_924_ == 0)
{
lean_object* v___x_925_; lean_object* v___f_926_; lean_object* v___x_927_; 
v___x_925_ = lean_box(v___x_924_);
v___f_926_ = lean_alloc_closure((void*)(l_Lean_Meta_PProdN_mkLambdas___lam__0___boxed), 9, 2);
lean_closure_set(v___f_926_, 0, v_es_916_);
lean_closure_set(v___f_926_, 1, v___x_925_);
v___x_927_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___redArg(v_type_915_, v___f_926_, v___x_924_, v_a_917_, v_a_918_, v_a_919_, v_a_920_);
return v___x_927_;
}
else
{
lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
lean_dec_ref(v_type_915_);
v___x_928_ = lean_unsigned_to_nat(0u);
v___x_929_ = lean_array_fget(v_es_916_, v___x_928_);
lean_dec_ref(v_es_916_);
v___x_930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_930_, 0, v___x_929_);
return v___x_930_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_mkLambdas___boxed(lean_object* v_type_931_, lean_object* v_es_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l_Lean_Meta_PProdN_mkLambdas(v_type_931_, v_es_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_);
lean_dec(v_a_936_);
lean_dec_ref(v_a_935_);
lean_dec(v_a_934_);
lean_dec_ref(v_a_933_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_stripProjs(lean_object* v_e_939_){
_start:
{
if (lean_obj_tag(v_e_939_) == 11)
{
lean_object* v_typeName_940_; 
v_typeName_940_ = lean_ctor_get(v_e_939_, 0);
if (lean_obj_tag(v_typeName_940_) == 1)
{
lean_object* v_pre_941_; 
v_pre_941_ = lean_ctor_get(v_typeName_940_, 0);
if (lean_obj_tag(v_pre_941_) == 0)
{
lean_object* v_struct_942_; lean_object* v_str_943_; lean_object* v___x_944_; uint8_t v___x_945_; 
v_struct_942_ = lean_ctor_get(v_e_939_, 2);
v_str_943_ = lean_ctor_get(v_typeName_940_, 1);
v___x_944_ = ((lean_object*)(l_Lean_Meta_mkPProd___closed__0));
v___x_945_ = lean_string_dec_eq(v_str_943_, v___x_944_);
if (v___x_945_ == 0)
{
lean_object* v___x_946_; uint8_t v___x_947_; 
v___x_946_ = ((lean_object*)(l_Lean_Meta_mkPProd___closed__2));
v___x_947_ = lean_string_dec_eq(v_str_943_, v___x_946_);
if (v___x_947_ == 0)
{
lean_inc_ref(v_e_939_);
return v_e_939_;
}
else
{
v_e_939_ = v_struct_942_;
goto _start;
}
}
else
{
v_e_939_ = v_struct_942_;
goto _start;
}
}
else
{
lean_inc_ref(v_e_939_);
return v_e_939_;
}
}
else
{
lean_inc_ref(v_e_939_);
return v_e_939_;
}
}
else
{
lean_inc_ref(v_e_939_);
return v_e_939_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_stripProjs___boxed(lean_object* v_e_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_Lean_Meta_PProdN_stripProjs(v_e_950_);
lean_dec_ref(v_e_950_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___redArg(lean_object* v_e_954_, lean_object* v_i_955_){
_start:
{
uint8_t v___y_958_; lean_object* v___x_972_; lean_object* v___x_973_; uint8_t v___x_974_; 
v___x_972_ = ((lean_object*)(l_Lean_Meta_mkPProdMk___closed__1));
v___x_973_ = lean_unsigned_to_nat(4u);
v___x_974_ = l_Lean_Expr_isAppOfArity(v_e_954_, v___x_972_, v___x_973_);
if (v___x_974_ == 0)
{
lean_object* v___x_975_; lean_object* v___x_976_; uint8_t v___x_977_; 
v___x_975_ = ((lean_object*)(l_Lean_Meta_mkPProdMk___closed__3));
v___x_976_ = lean_unsigned_to_nat(2u);
v___x_977_ = l_Lean_Expr_isAppOfArity(v_e_954_, v___x_975_, v___x_976_);
v___y_958_ = v___x_977_;
goto v___jp_957_;
}
else
{
v___y_958_ = v___x_974_;
goto v___jp_957_;
}
v___jp_957_:
{
if (v___y_958_ == 0)
{
lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_959_ = ((lean_object*)(l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___redArg___closed__0));
v___x_960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_960_, 0, v___x_959_);
return v___x_960_;
}
else
{
lean_object* v___x_961_; uint8_t v___x_962_; 
v___x_961_ = lean_unsigned_to_nat(0u);
v___x_962_ = lean_nat_dec_eq(v_i_955_, v___x_961_);
if (v___x_962_ == 0)
{
lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; 
v___x_963_ = l_Lean_Expr_appArg_x21(v_e_954_);
v___x_964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_964_, 0, v___x_963_);
v___x_965_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_965_, 0, v___x_964_);
v___x_966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_966_, 0, v___x_965_);
return v___x_966_;
}
else
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_967_ = l_Lean_Expr_appFn_x21(v_e_954_);
v___x_968_ = l_Lean_Expr_appArg_x21(v___x_967_);
lean_dec_ref(v___x_967_);
v___x_969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_969_, 0, v___x_968_);
v___x_970_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_970_, 0, v___x_969_);
v___x_971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_971_, 0, v___x_970_);
return v___x_971_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___redArg___boxed(lean_object* v_e_978_, lean_object* v_i_979_, lean_object* v_a_980_){
_start:
{
lean_object* v_res_981_; 
v_res_981_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___redArg(v_e_978_, v_i_979_);
lean_dec(v_i_979_);
lean_dec_ref(v_e_978_);
return v_res_981_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce(lean_object* v_e_982_, lean_object* v_i_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_){
_start:
{
lean_object* v___x_989_; 
v___x_989_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___redArg(v_e_982_, v_i_983_);
return v___x_989_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___boxed(lean_object* v_e_990_, lean_object* v_i_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_){
_start:
{
lean_object* v_res_997_; 
v_res_997_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce(v_e_990_, v_i_991_, v_a_992_, v_a_993_, v_a_994_, v_a_995_);
lean_dec(v_a_995_);
lean_dec_ref(v_a_994_);
lean_dec(v_a_993_);
lean_dec_ref(v_a_992_);
lean_dec(v_i_991_);
lean_dec_ref(v_e_990_);
return v_res_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_reduceProjs___lam__0(lean_object* v_x_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_){
_start:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_1004_ = ((lean_object*)(l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___redArg___closed__0));
v___x_1005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1004_);
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_reduceProjs___lam__0___boxed(lean_object* v_x_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l_Lean_Meta_PProdN_reduceProjs___lam__0(v_x_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_);
lean_dec(v___y_1010_);
lean_dec_ref(v___y_1009_);
lean_dec(v___y_1008_);
lean_dec_ref(v___y_1007_);
lean_dec_ref(v_x_1006_);
return v_res_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_reduceProjs___lam__1(lean_object* v_e_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_){
_start:
{
lean_object* v_e_x27_1036_; lean_object* v_e_x27_1040_; lean_object* v___x_1043_; 
lean_inc_ref(v_e_1029_);
v___x_1043_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1029_, v___y_1031_);
if (lean_obj_tag(v___x_1043_) == 0)
{
lean_object* v_a_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1073_; 
v_a_1044_ = lean_ctor_get(v___x_1043_, 0);
v_isSharedCheck_1073_ = !lean_is_exclusive(v___x_1043_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1046_ = v___x_1043_;
v_isShared_1047_ = v_isSharedCheck_1073_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_a_1044_);
lean_dec(v___x_1043_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1073_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1057_; uint8_t v___x_1058_; 
v___x_1057_ = l_Lean_Expr_cleanupAnnotations(v_a_1044_);
v___x_1058_ = l_Lean_Expr_isApp(v___x_1057_);
if (v___x_1058_ == 0)
{
lean_dec_ref(v___x_1057_);
goto v___jp_1048_;
}
else
{
lean_object* v_arg_1059_; lean_object* v___x_1060_; uint8_t v___x_1061_; 
v_arg_1059_ = lean_ctor_get(v___x_1057_, 1);
lean_inc_ref(v_arg_1059_);
v___x_1060_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1057_);
v___x_1061_ = l_Lean_Expr_isApp(v___x_1060_);
if (v___x_1061_ == 0)
{
lean_dec_ref(v___x_1060_);
lean_dec_ref(v_arg_1059_);
goto v___jp_1048_;
}
else
{
lean_object* v___x_1062_; uint8_t v___x_1063_; 
v___x_1062_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1060_);
v___x_1063_ = l_Lean_Expr_isApp(v___x_1062_);
if (v___x_1063_ == 0)
{
lean_dec_ref(v___x_1062_);
lean_dec_ref(v_arg_1059_);
goto v___jp_1048_;
}
else
{
lean_object* v___x_1064_; lean_object* v___x_1065_; uint8_t v___x_1066_; 
v___x_1064_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1062_);
v___x_1065_ = ((lean_object*)(l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__1));
v___x_1066_ = l_Lean_Expr_isConstOf(v___x_1064_, v___x_1065_);
if (v___x_1066_ == 0)
{
lean_object* v___x_1067_; uint8_t v___x_1068_; 
v___x_1067_ = ((lean_object*)(l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__3));
v___x_1068_ = l_Lean_Expr_isConstOf(v___x_1064_, v___x_1067_);
if (v___x_1068_ == 0)
{
lean_object* v___x_1069_; uint8_t v___x_1070_; 
v___x_1069_ = ((lean_object*)(l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__5));
v___x_1070_ = l_Lean_Expr_isConstOf(v___x_1064_, v___x_1069_);
if (v___x_1070_ == 0)
{
lean_object* v___x_1071_; uint8_t v___x_1072_; 
v___x_1071_ = ((lean_object*)(l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__7));
v___x_1072_ = l_Lean_Expr_isConstOf(v___x_1064_, v___x_1071_);
lean_dec_ref(v___x_1064_);
if (v___x_1072_ == 0)
{
lean_dec_ref(v_arg_1059_);
goto v___jp_1048_;
}
else
{
lean_del_object(v___x_1046_);
lean_dec_ref(v_e_1029_);
v_e_x27_1036_ = v_arg_1059_;
goto v___jp_1035_;
}
}
else
{
lean_dec_ref(v___x_1064_);
lean_del_object(v___x_1046_);
lean_dec_ref(v_e_1029_);
v_e_x27_1036_ = v_arg_1059_;
goto v___jp_1035_;
}
}
else
{
lean_dec_ref(v___x_1064_);
lean_del_object(v___x_1046_);
lean_dec_ref(v_e_1029_);
v_e_x27_1040_ = v_arg_1059_;
goto v___jp_1039_;
}
}
else
{
lean_dec_ref(v___x_1064_);
lean_del_object(v___x_1046_);
lean_dec_ref(v_e_1029_);
v_e_x27_1040_ = v_arg_1059_;
goto v___jp_1039_;
}
}
}
}
v___jp_1048_:
{
uint8_t v___x_1049_; 
v___x_1049_ = l_Lean_Expr_isProj(v_e_1029_);
if (v___x_1049_ == 0)
{
lean_object* v___x_1050_; lean_object* v___x_1052_; 
lean_dec_ref(v_e_1029_);
v___x_1050_ = ((lean_object*)(l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___redArg___closed__0));
if (v_isShared_1047_ == 0)
{
lean_ctor_set(v___x_1046_, 0, v___x_1050_);
v___x_1052_ = v___x_1046_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v___x_1050_);
v___x_1052_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
return v___x_1052_;
}
}
else
{
lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; 
lean_del_object(v___x_1046_);
v___x_1054_ = l_Lean_Expr_projExpr_x21(v_e_1029_);
v___x_1055_ = l_Lean_Expr_projIdx_x21(v_e_1029_);
lean_dec_ref(v_e_1029_);
v___x_1056_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___redArg(v___x_1054_, v___x_1055_);
lean_dec(v___x_1055_);
lean_dec_ref(v___x_1054_);
return v___x_1056_;
}
}
}
}
else
{
lean_object* v_a_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1081_; 
lean_dec_ref(v_e_1029_);
v_a_1074_ = lean_ctor_get(v___x_1043_, 0);
v_isSharedCheck_1081_ = !lean_is_exclusive(v___x_1043_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1076_ = v___x_1043_;
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_a_1074_);
lean_dec(v___x_1043_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1079_; 
if (v_isShared_1077_ == 0)
{
v___x_1079_ = v___x_1076_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v_a_1074_);
v___x_1079_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
return v___x_1079_;
}
}
}
v___jp_1035_:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1037_ = lean_unsigned_to_nat(0u);
v___x_1038_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___redArg(v_e_x27_1036_, v___x_1037_);
lean_dec_ref(v_e_x27_1036_);
return v___x_1038_;
}
v___jp_1039_:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1041_ = lean_unsigned_to_nat(1u);
v___x_1042_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___redArg(v_e_x27_1040_, v___x_1041_);
lean_dec_ref(v_e_x27_1040_);
return v___x_1042_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_reduceProjs___lam__1___boxed(lean_object* v_e_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l_Lean_Meta_PProdN_reduceProjs___lam__1(v_e_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_);
lean_dec(v___y_1086_);
lean_dec_ref(v___y_1085_);
lean_dec(v___y_1084_);
lean_dec_ref(v___y_1083_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3_spec__4___redArg(lean_object* v_a_1089_, lean_object* v_x_1090_){
_start:
{
if (lean_obj_tag(v_x_1090_) == 0)
{
lean_object* v___x_1091_; 
v___x_1091_ = lean_box(0);
return v___x_1091_;
}
else
{
lean_object* v_key_1092_; lean_object* v_value_1093_; lean_object* v_tail_1094_; uint8_t v___x_1095_; 
v_key_1092_ = lean_ctor_get(v_x_1090_, 0);
v_value_1093_ = lean_ctor_get(v_x_1090_, 1);
v_tail_1094_ = lean_ctor_get(v_x_1090_, 2);
v___x_1095_ = l_Lean_ExprStructEq_beq(v_key_1092_, v_a_1089_);
if (v___x_1095_ == 0)
{
v_x_1090_ = v_tail_1094_;
goto _start;
}
else
{
lean_object* v___x_1097_; 
lean_inc(v_value_1093_);
v___x_1097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1097_, 0, v_value_1093_);
return v___x_1097_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object* v_a_1098_, lean_object* v_x_1099_){
_start:
{
lean_object* v_res_1100_; 
v_res_1100_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3_spec__4___redArg(v_a_1098_, v_x_1099_);
lean_dec(v_x_1099_);
lean_dec_ref(v_a_1098_);
return v_res_1100_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3___redArg(lean_object* v_m_1101_, lean_object* v_a_1102_){
_start:
{
lean_object* v_buckets_1103_; lean_object* v___x_1104_; uint64_t v___x_1105_; uint64_t v___x_1106_; uint64_t v___x_1107_; uint64_t v_fold_1108_; uint64_t v___x_1109_; uint64_t v___x_1110_; uint64_t v___x_1111_; size_t v___x_1112_; size_t v___x_1113_; size_t v___x_1114_; size_t v___x_1115_; size_t v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; 
v_buckets_1103_ = lean_ctor_get(v_m_1101_, 1);
v___x_1104_ = lean_array_get_size(v_buckets_1103_);
v___x_1105_ = l_Lean_ExprStructEq_hash(v_a_1102_);
v___x_1106_ = 32ULL;
v___x_1107_ = lean_uint64_shift_right(v___x_1105_, v___x_1106_);
v_fold_1108_ = lean_uint64_xor(v___x_1105_, v___x_1107_);
v___x_1109_ = 16ULL;
v___x_1110_ = lean_uint64_shift_right(v_fold_1108_, v___x_1109_);
v___x_1111_ = lean_uint64_xor(v_fold_1108_, v___x_1110_);
v___x_1112_ = lean_uint64_to_usize(v___x_1111_);
v___x_1113_ = lean_usize_of_nat(v___x_1104_);
v___x_1114_ = ((size_t)1ULL);
v___x_1115_ = lean_usize_sub(v___x_1113_, v___x_1114_);
v___x_1116_ = lean_usize_land(v___x_1112_, v___x_1115_);
v___x_1117_ = lean_array_uget_borrowed(v_buckets_1103_, v___x_1116_);
v___x_1118_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3_spec__4___redArg(v_a_1102_, v___x_1117_);
return v___x_1118_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_m_1119_, lean_object* v_a_1120_){
_start:
{
lean_object* v_res_1121_; 
v_res_1121_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3___redArg(v_m_1119_, v_a_1120_);
lean_dec_ref(v_a_1120_);
lean_dec_ref(v_m_1119_);
return v_res_1121_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__12___redArg(lean_object* v_a_1122_, lean_object* v_b_1123_, lean_object* v_x_1124_){
_start:
{
if (lean_obj_tag(v_x_1124_) == 0)
{
lean_dec(v_b_1123_);
lean_dec_ref(v_a_1122_);
return v_x_1124_;
}
else
{
lean_object* v_key_1125_; lean_object* v_value_1126_; lean_object* v_tail_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1139_; 
v_key_1125_ = lean_ctor_get(v_x_1124_, 0);
v_value_1126_ = lean_ctor_get(v_x_1124_, 1);
v_tail_1127_ = lean_ctor_get(v_x_1124_, 2);
v_isSharedCheck_1139_ = !lean_is_exclusive(v_x_1124_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1129_ = v_x_1124_;
v_isShared_1130_ = v_isSharedCheck_1139_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_tail_1127_);
lean_inc(v_value_1126_);
lean_inc(v_key_1125_);
lean_dec(v_x_1124_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1139_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
uint8_t v___x_1131_; 
v___x_1131_ = l_Lean_ExprStructEq_beq(v_key_1125_, v_a_1122_);
if (v___x_1131_ == 0)
{
lean_object* v___x_1132_; lean_object* v___x_1134_; 
v___x_1132_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__12___redArg(v_a_1122_, v_b_1123_, v_tail_1127_);
if (v_isShared_1130_ == 0)
{
lean_ctor_set(v___x_1129_, 2, v___x_1132_);
v___x_1134_ = v___x_1129_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v_key_1125_);
lean_ctor_set(v_reuseFailAlloc_1135_, 1, v_value_1126_);
lean_ctor_set(v_reuseFailAlloc_1135_, 2, v___x_1132_);
v___x_1134_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
return v___x_1134_;
}
}
else
{
lean_object* v___x_1137_; 
lean_dec(v_value_1126_);
lean_dec(v_key_1125_);
if (v_isShared_1130_ == 0)
{
lean_ctor_set(v___x_1129_, 1, v_b_1123_);
lean_ctor_set(v___x_1129_, 0, v_a_1122_);
v___x_1137_ = v___x_1129_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_a_1122_);
lean_ctor_set(v_reuseFailAlloc_1138_, 1, v_b_1123_);
lean_ctor_set(v_reuseFailAlloc_1138_, 2, v_tail_1127_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
return v___x_1137_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(lean_object* v_x_1140_, lean_object* v_x_1141_){
_start:
{
if (lean_obj_tag(v_x_1141_) == 0)
{
return v_x_1140_;
}
else
{
lean_object* v_key_1142_; lean_object* v_value_1143_; lean_object* v_tail_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1167_; 
v_key_1142_ = lean_ctor_get(v_x_1141_, 0);
v_value_1143_ = lean_ctor_get(v_x_1141_, 1);
v_tail_1144_ = lean_ctor_get(v_x_1141_, 2);
v_isSharedCheck_1167_ = !lean_is_exclusive(v_x_1141_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1146_ = v_x_1141_;
v_isShared_1147_ = v_isSharedCheck_1167_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_tail_1144_);
lean_inc(v_value_1143_);
lean_inc(v_key_1142_);
lean_dec(v_x_1141_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1167_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v___x_1148_; uint64_t v___x_1149_; uint64_t v___x_1150_; uint64_t v___x_1151_; uint64_t v_fold_1152_; uint64_t v___x_1153_; uint64_t v___x_1154_; uint64_t v___x_1155_; size_t v___x_1156_; size_t v___x_1157_; size_t v___x_1158_; size_t v___x_1159_; size_t v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1163_; 
v___x_1148_ = lean_array_get_size(v_x_1140_);
v___x_1149_ = l_Lean_ExprStructEq_hash(v_key_1142_);
v___x_1150_ = 32ULL;
v___x_1151_ = lean_uint64_shift_right(v___x_1149_, v___x_1150_);
v_fold_1152_ = lean_uint64_xor(v___x_1149_, v___x_1151_);
v___x_1153_ = 16ULL;
v___x_1154_ = lean_uint64_shift_right(v_fold_1152_, v___x_1153_);
v___x_1155_ = lean_uint64_xor(v_fold_1152_, v___x_1154_);
v___x_1156_ = lean_uint64_to_usize(v___x_1155_);
v___x_1157_ = lean_usize_of_nat(v___x_1148_);
v___x_1158_ = ((size_t)1ULL);
v___x_1159_ = lean_usize_sub(v___x_1157_, v___x_1158_);
v___x_1160_ = lean_usize_land(v___x_1156_, v___x_1159_);
v___x_1161_ = lean_array_uget_borrowed(v_x_1140_, v___x_1160_);
lean_inc(v___x_1161_);
if (v_isShared_1147_ == 0)
{
lean_ctor_set(v___x_1146_, 2, v___x_1161_);
v___x_1163_ = v___x_1146_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_key_1142_);
lean_ctor_set(v_reuseFailAlloc_1166_, 1, v_value_1143_);
lean_ctor_set(v_reuseFailAlloc_1166_, 2, v___x_1161_);
v___x_1163_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
lean_object* v___x_1164_; 
v___x_1164_ = lean_array_uset(v_x_1140_, v___x_1160_, v___x_1163_);
v_x_1140_ = v___x_1164_;
v_x_1141_ = v_tail_1144_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(lean_object* v_i_1168_, lean_object* v_source_1169_, lean_object* v_target_1170_){
_start:
{
lean_object* v___x_1171_; uint8_t v___x_1172_; 
v___x_1171_ = lean_array_get_size(v_source_1169_);
v___x_1172_ = lean_nat_dec_lt(v_i_1168_, v___x_1171_);
if (v___x_1172_ == 0)
{
lean_dec_ref(v_source_1169_);
lean_dec(v_i_1168_);
return v_target_1170_;
}
else
{
lean_object* v_es_1173_; lean_object* v___x_1174_; lean_object* v_source_1175_; lean_object* v_target_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; 
v_es_1173_ = lean_array_fget(v_source_1169_, v_i_1168_);
v___x_1174_ = lean_box(0);
v_source_1175_ = lean_array_fset(v_source_1169_, v_i_1168_, v___x_1174_);
v_target_1176_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_target_1170_, v_es_1173_);
v___x_1177_ = lean_unsigned_to_nat(1u);
v___x_1178_ = lean_nat_add(v_i_1168_, v___x_1177_);
lean_dec(v_i_1168_);
v_i_1168_ = v___x_1178_;
v_source_1169_ = v_source_1175_;
v_target_1170_ = v_target_1176_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11___redArg(lean_object* v_data_1180_){
_start:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v_nbuckets_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___x_1181_ = lean_array_get_size(v_data_1180_);
v___x_1182_ = lean_unsigned_to_nat(2u);
v_nbuckets_1183_ = lean_nat_mul(v___x_1181_, v___x_1182_);
v___x_1184_ = lean_unsigned_to_nat(0u);
v___x_1185_ = lean_box(0);
v___x_1186_ = lean_mk_array(v_nbuckets_1183_, v___x_1185_);
v___x_1187_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v___x_1184_, v_data_1180_, v___x_1186_);
return v___x_1187_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__10___redArg(lean_object* v_a_1188_, lean_object* v_x_1189_){
_start:
{
if (lean_obj_tag(v_x_1189_) == 0)
{
uint8_t v___x_1190_; 
v___x_1190_ = 0;
return v___x_1190_;
}
else
{
lean_object* v_key_1191_; lean_object* v_tail_1192_; uint8_t v___x_1193_; 
v_key_1191_ = lean_ctor_get(v_x_1189_, 0);
v_tail_1192_ = lean_ctor_get(v_x_1189_, 2);
v___x_1193_ = l_Lean_ExprStructEq_beq(v_key_1191_, v_a_1188_);
if (v___x_1193_ == 0)
{
v_x_1189_ = v_tail_1192_;
goto _start;
}
else
{
return v___x_1193_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__10___redArg___boxed(lean_object* v_a_1195_, lean_object* v_x_1196_){
_start:
{
uint8_t v_res_1197_; lean_object* v_r_1198_; 
v_res_1197_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__10___redArg(v_a_1195_, v_x_1196_);
lean_dec(v_x_1196_);
lean_dec_ref(v_a_1195_);
v_r_1198_ = lean_box(v_res_1197_);
return v_r_1198_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6___redArg(lean_object* v_m_1199_, lean_object* v_a_1200_, lean_object* v_b_1201_){
_start:
{
lean_object* v_size_1202_; lean_object* v_buckets_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1246_; 
v_size_1202_ = lean_ctor_get(v_m_1199_, 0);
v_buckets_1203_ = lean_ctor_get(v_m_1199_, 1);
v_isSharedCheck_1246_ = !lean_is_exclusive(v_m_1199_);
if (v_isSharedCheck_1246_ == 0)
{
v___x_1205_ = v_m_1199_;
v_isShared_1206_ = v_isSharedCheck_1246_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_buckets_1203_);
lean_inc(v_size_1202_);
lean_dec(v_m_1199_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1246_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1207_; uint64_t v___x_1208_; uint64_t v___x_1209_; uint64_t v___x_1210_; uint64_t v_fold_1211_; uint64_t v___x_1212_; uint64_t v___x_1213_; uint64_t v___x_1214_; size_t v___x_1215_; size_t v___x_1216_; size_t v___x_1217_; size_t v___x_1218_; size_t v___x_1219_; lean_object* v_bkt_1220_; uint8_t v___x_1221_; 
v___x_1207_ = lean_array_get_size(v_buckets_1203_);
v___x_1208_ = l_Lean_ExprStructEq_hash(v_a_1200_);
v___x_1209_ = 32ULL;
v___x_1210_ = lean_uint64_shift_right(v___x_1208_, v___x_1209_);
v_fold_1211_ = lean_uint64_xor(v___x_1208_, v___x_1210_);
v___x_1212_ = 16ULL;
v___x_1213_ = lean_uint64_shift_right(v_fold_1211_, v___x_1212_);
v___x_1214_ = lean_uint64_xor(v_fold_1211_, v___x_1213_);
v___x_1215_ = lean_uint64_to_usize(v___x_1214_);
v___x_1216_ = lean_usize_of_nat(v___x_1207_);
v___x_1217_ = ((size_t)1ULL);
v___x_1218_ = lean_usize_sub(v___x_1216_, v___x_1217_);
v___x_1219_ = lean_usize_land(v___x_1215_, v___x_1218_);
v_bkt_1220_ = lean_array_uget_borrowed(v_buckets_1203_, v___x_1219_);
v___x_1221_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__10___redArg(v_a_1200_, v_bkt_1220_);
if (v___x_1221_ == 0)
{
lean_object* v___x_1222_; lean_object* v_size_x27_1223_; lean_object* v___x_1224_; lean_object* v_buckets_x27_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; uint8_t v___x_1231_; 
v___x_1222_ = lean_unsigned_to_nat(1u);
v_size_x27_1223_ = lean_nat_add(v_size_1202_, v___x_1222_);
lean_dec(v_size_1202_);
lean_inc(v_bkt_1220_);
v___x_1224_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1224_, 0, v_a_1200_);
lean_ctor_set(v___x_1224_, 1, v_b_1201_);
lean_ctor_set(v___x_1224_, 2, v_bkt_1220_);
v_buckets_x27_1225_ = lean_array_uset(v_buckets_1203_, v___x_1219_, v___x_1224_);
v___x_1226_ = lean_unsigned_to_nat(4u);
v___x_1227_ = lean_nat_mul(v_size_x27_1223_, v___x_1226_);
v___x_1228_ = lean_unsigned_to_nat(3u);
v___x_1229_ = lean_nat_div(v___x_1227_, v___x_1228_);
lean_dec(v___x_1227_);
v___x_1230_ = lean_array_get_size(v_buckets_x27_1225_);
v___x_1231_ = lean_nat_dec_le(v___x_1229_, v___x_1230_);
lean_dec(v___x_1229_);
if (v___x_1231_ == 0)
{
lean_object* v_val_1232_; lean_object* v___x_1234_; 
v_val_1232_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11___redArg(v_buckets_x27_1225_);
if (v_isShared_1206_ == 0)
{
lean_ctor_set(v___x_1205_, 1, v_val_1232_);
lean_ctor_set(v___x_1205_, 0, v_size_x27_1223_);
v___x_1234_ = v___x_1205_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v_size_x27_1223_);
lean_ctor_set(v_reuseFailAlloc_1235_, 1, v_val_1232_);
v___x_1234_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
return v___x_1234_;
}
}
else
{
lean_object* v___x_1237_; 
if (v_isShared_1206_ == 0)
{
lean_ctor_set(v___x_1205_, 1, v_buckets_x27_1225_);
lean_ctor_set(v___x_1205_, 0, v_size_x27_1223_);
v___x_1237_ = v___x_1205_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v_size_x27_1223_);
lean_ctor_set(v_reuseFailAlloc_1238_, 1, v_buckets_x27_1225_);
v___x_1237_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
return v___x_1237_;
}
}
}
else
{
lean_object* v___x_1239_; lean_object* v_buckets_x27_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1244_; 
lean_inc(v_bkt_1220_);
v___x_1239_ = lean_box(0);
v_buckets_x27_1240_ = lean_array_uset(v_buckets_1203_, v___x_1219_, v___x_1239_);
v___x_1241_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__12___redArg(v_a_1200_, v_b_1201_, v_bkt_1220_);
v___x_1242_ = lean_array_uset(v_buckets_x27_1240_, v___x_1219_, v___x_1241_);
if (v_isShared_1206_ == 0)
{
lean_ctor_set(v___x_1205_, 1, v___x_1242_);
v___x_1244_ = v___x_1205_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_size_1202_);
lean_ctor_set(v_reuseFailAlloc_1245_, 1, v___x_1242_);
v___x_1244_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
return v___x_1244_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__2(lean_object* v_a_1247_, lean_object* v_e_1248_, lean_object* v_a_1249_){
_start:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___x_1251_ = lean_st_ref_take(v_a_1247_);
v___x_1252_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6___redArg(v___x_1251_, v_e_1248_, v_a_1249_);
v___x_1253_ = lean_st_ref_set(v_a_1247_, v___x_1252_);
v___x_1254_ = lean_box(0);
return v___x_1254_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__2___boxed(lean_object* v_a_1255_, lean_object* v_e_1256_, lean_object* v_a_1257_, lean_object* v___y_1258_){
_start:
{
lean_object* v_res_1259_; 
v_res_1259_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__2(v_a_1255_, v_e_1256_, v_a_1257_);
lean_dec(v_a_1255_);
return v_res_1259_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_1260_, lean_object* v_x_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_){
_start:
{
lean_object* v___x_1267_; lean_object* v___x_1268_; 
v___x_1267_ = lean_apply_1(v_x_1261_, lean_box(0));
v___x_1268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1268_, 0, v___x_1267_);
return v___x_1268_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_1269_, lean_object* v_x_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_){
_start:
{
lean_object* v_res_1276_; 
v_res_1276_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__0(v_00_u03b1_1269_, v_x_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_);
lean_dec(v___y_1274_);
lean_dec_ref(v___y_1273_);
lean_dec(v___y_1272_);
lean_dec_ref(v___y_1271_);
return v_res_1276_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1277_ = lean_box(0);
v___x_1278_ = l_Lean_interruptExceptionId;
v___x_1279_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1278_);
lean_ctor_set(v___x_1279_, 1, v___x_1277_);
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__8___redArg(){
_start:
{
lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1281_ = lean_obj_once(&l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__8___redArg___closed__0, &l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__8___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__8___redArg___closed__0);
v___x_1282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1282_, 0, v___x_1281_);
return v___x_1282_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__8___redArg___boxed(lean_object* v___y_1283_){
_start:
{
lean_object* v_res_1284_; 
v_res_1284_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__8___redArg();
return v_res_1284_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1290_ = l_Lean_maxRecDepthErrorMessage;
v___x_1291_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1291_, 0, v___x_1290_);
return v___x_1291_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_1292_; lean_object* v___x_1293_; 
v___x_1292_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__3);
v___x_1293_ = l_Lean_MessageData_ofFormat(v___x_1292_);
return v___x_1293_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; 
v___x_1294_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__4);
v___x_1295_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__2));
v___x_1296_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1296_, 0, v___x_1295_);
lean_ctor_set(v___x_1296_, 1, v___x_1294_);
return v___x_1296_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg(lean_object* v_ref_1297_){
_start:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; 
v___x_1299_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__5);
v___x_1300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1300_, 0, v_ref_1297_);
lean_ctor_set(v___x_1300_, 1, v___x_1299_);
v___x_1301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1301_, 0, v___x_1300_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object* v_ref_1302_, lean_object* v___y_1303_){
_start:
{
lean_object* v_res_1304_; 
v_res_1304_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_1302_);
return v_res_1304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5___redArg(lean_object* v_x_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_){
_start:
{
lean_object* v___y_1313_; lean_object* v___y_1323_; lean_object* v___y_1324_; lean_object* v___y_1325_; lean_object* v___y_1326_; lean_object* v___y_1327_; lean_object* v___y_1328_; lean_object* v___y_1329_; uint8_t v___y_1330_; lean_object* v___y_1331_; lean_object* v___y_1332_; lean_object* v___y_1333_; lean_object* v___y_1334_; lean_object* v___y_1335_; lean_object* v___y_1336_; lean_object* v___y_1337_; uint8_t v___y_1338_; uint8_t v___y_1339_; lean_object* v_fileName_1345_; lean_object* v_fileMap_1346_; lean_object* v_options_1347_; lean_object* v_currRecDepth_1348_; lean_object* v_maxRecDepth_1349_; lean_object* v_ref_1350_; lean_object* v_currNamespace_1351_; lean_object* v_openDecls_1352_; lean_object* v_initHeartbeats_1353_; lean_object* v_maxHeartbeats_1354_; lean_object* v_quotContext_1355_; lean_object* v_currMacroScope_1356_; uint8_t v_diag_1357_; lean_object* v_cancelTk_x3f_1358_; uint8_t v_suppressElabErrors_1359_; lean_object* v_inheritedTraceOptions_1360_; 
v_fileName_1345_ = lean_ctor_get(v___y_1309_, 0);
v_fileMap_1346_ = lean_ctor_get(v___y_1309_, 1);
v_options_1347_ = lean_ctor_get(v___y_1309_, 2);
v_currRecDepth_1348_ = lean_ctor_get(v___y_1309_, 3);
v_maxRecDepth_1349_ = lean_ctor_get(v___y_1309_, 4);
v_ref_1350_ = lean_ctor_get(v___y_1309_, 5);
v_currNamespace_1351_ = lean_ctor_get(v___y_1309_, 6);
v_openDecls_1352_ = lean_ctor_get(v___y_1309_, 7);
v_initHeartbeats_1353_ = lean_ctor_get(v___y_1309_, 8);
v_maxHeartbeats_1354_ = lean_ctor_get(v___y_1309_, 9);
v_quotContext_1355_ = lean_ctor_get(v___y_1309_, 10);
v_currMacroScope_1356_ = lean_ctor_get(v___y_1309_, 11);
v_diag_1357_ = lean_ctor_get_uint8(v___y_1309_, sizeof(void*)*14);
v_cancelTk_x3f_1358_ = lean_ctor_get(v___y_1309_, 12);
v_suppressElabErrors_1359_ = lean_ctor_get_uint8(v___y_1309_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1360_ = lean_ctor_get(v___y_1309_, 13);
if (lean_obj_tag(v_cancelTk_x3f_1358_) == 1)
{
lean_object* v_val_1366_; uint8_t v___x_1367_; 
v_val_1366_ = lean_ctor_get(v_cancelTk_x3f_1358_, 0);
v___x_1367_ = l_IO_CancelToken_isSet(v_val_1366_);
if (v___x_1367_ == 0)
{
goto v___jp_1361_;
}
else
{
lean_object* v___x_1368_; lean_object* v_a_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1376_; 
lean_dec_ref(v_x_1305_);
v___x_1368_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__8___redArg();
v_a_1369_ = lean_ctor_get(v___x_1368_, 0);
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1371_ = v___x_1368_;
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_a_1369_);
lean_dec(v___x_1368_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1374_; 
if (v_isShared_1372_ == 0)
{
v___x_1374_ = v___x_1371_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v_a_1369_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
}
}
}
}
else
{
goto v___jp_1361_;
}
v___jp_1312_:
{
if (lean_obj_tag(v___y_1313_) == 0)
{
return v___y_1313_;
}
else
{
lean_object* v_a_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1321_; 
v_a_1314_ = lean_ctor_get(v___y_1313_, 0);
v_isSharedCheck_1321_ = !lean_is_exclusive(v___y_1313_);
if (v_isSharedCheck_1321_ == 0)
{
v___x_1316_ = v___y_1313_;
v_isShared_1317_ = v_isSharedCheck_1321_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_a_1314_);
lean_dec(v___y_1313_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1321_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v___x_1319_; 
if (v_isShared_1317_ == 0)
{
v___x_1319_ = v___x_1316_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v_a_1314_);
v___x_1319_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
return v___x_1319_;
}
}
}
}
v___jp_1322_:
{
if (v___y_1339_ == 0)
{
lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___x_1340_ = lean_unsigned_to_nat(1u);
v___x_1341_ = lean_nat_add(v___y_1335_, v___x_1340_);
lean_inc_ref(v___y_1323_);
lean_inc(v___y_1325_);
lean_inc(v___y_1333_);
lean_inc(v___y_1334_);
lean_inc(v___y_1332_);
lean_inc(v___y_1328_);
lean_inc(v___y_1326_);
lean_inc(v___y_1337_);
lean_inc(v___y_1327_);
lean_inc(v___y_1324_);
lean_inc_ref(v___y_1336_);
lean_inc_ref(v___y_1331_);
lean_inc_ref(v___y_1329_);
v___x_1342_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1342_, 0, v___y_1329_);
lean_ctor_set(v___x_1342_, 1, v___y_1331_);
lean_ctor_set(v___x_1342_, 2, v___y_1336_);
lean_ctor_set(v___x_1342_, 3, v___x_1341_);
lean_ctor_set(v___x_1342_, 4, v___y_1324_);
lean_ctor_set(v___x_1342_, 5, v___y_1327_);
lean_ctor_set(v___x_1342_, 6, v___y_1337_);
lean_ctor_set(v___x_1342_, 7, v___y_1326_);
lean_ctor_set(v___x_1342_, 8, v___y_1328_);
lean_ctor_set(v___x_1342_, 9, v___y_1332_);
lean_ctor_set(v___x_1342_, 10, v___y_1334_);
lean_ctor_set(v___x_1342_, 11, v___y_1333_);
lean_ctor_set(v___x_1342_, 12, v___y_1325_);
lean_ctor_set(v___x_1342_, 13, v___y_1323_);
lean_ctor_set_uint8(v___x_1342_, sizeof(void*)*14, v___y_1330_);
lean_ctor_set_uint8(v___x_1342_, sizeof(void*)*14 + 1, v___y_1338_);
lean_inc(v___y_1310_);
lean_inc(v___y_1308_);
lean_inc_ref(v___y_1307_);
lean_inc(v___y_1306_);
v___x_1343_ = lean_apply_6(v_x_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___x_1342_, v___y_1310_, lean_box(0));
v___y_1313_ = v___x_1343_;
goto v___jp_1312_;
}
else
{
lean_object* v___x_1344_; 
lean_dec_ref(v_x_1305_);
lean_inc(v___y_1327_);
v___x_1344_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg(v___y_1327_);
v___y_1313_ = v___x_1344_;
goto v___jp_1312_;
}
}
v___jp_1361_:
{
lean_object* v___x_1362_; uint8_t v___x_1363_; uint8_t v___x_1364_; 
v___x_1362_ = lean_unsigned_to_nat(0u);
v___x_1363_ = lean_nat_dec_eq(v_maxRecDepth_1349_, v___x_1362_);
v___x_1364_ = lean_bool_not(v___x_1363_);
if (v___x_1364_ == 0)
{
v___y_1323_ = v_inheritedTraceOptions_1360_;
v___y_1324_ = v_maxRecDepth_1349_;
v___y_1325_ = v_cancelTk_x3f_1358_;
v___y_1326_ = v_openDecls_1352_;
v___y_1327_ = v_ref_1350_;
v___y_1328_ = v_initHeartbeats_1353_;
v___y_1329_ = v_fileName_1345_;
v___y_1330_ = v_diag_1357_;
v___y_1331_ = v_fileMap_1346_;
v___y_1332_ = v_maxHeartbeats_1354_;
v___y_1333_ = v_currMacroScope_1356_;
v___y_1334_ = v_quotContext_1355_;
v___y_1335_ = v_currRecDepth_1348_;
v___y_1336_ = v_options_1347_;
v___y_1337_ = v_currNamespace_1351_;
v___y_1338_ = v_suppressElabErrors_1359_;
v___y_1339_ = v___x_1364_;
goto v___jp_1322_;
}
else
{
uint8_t v___x_1365_; 
v___x_1365_ = lean_nat_dec_eq(v_currRecDepth_1348_, v_maxRecDepth_1349_);
v___y_1323_ = v_inheritedTraceOptions_1360_;
v___y_1324_ = v_maxRecDepth_1349_;
v___y_1325_ = v_cancelTk_x3f_1358_;
v___y_1326_ = v_openDecls_1352_;
v___y_1327_ = v_ref_1350_;
v___y_1328_ = v_initHeartbeats_1353_;
v___y_1329_ = v_fileName_1345_;
v___y_1330_ = v_diag_1357_;
v___y_1331_ = v_fileMap_1346_;
v___y_1332_ = v_maxHeartbeats_1354_;
v___y_1333_ = v_currMacroScope_1356_;
v___y_1334_ = v_quotContext_1355_;
v___y_1335_ = v_currRecDepth_1348_;
v___y_1336_ = v_options_1347_;
v___y_1337_ = v_currNamespace_1351_;
v___y_1338_ = v_suppressElabErrors_1359_;
v___y_1339_ = v___x_1365_;
goto v___jp_1322_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_x_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_){
_start:
{
lean_object* v_res_1384_; 
v_res_1384_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5___redArg(v_x_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_);
lean_dec(v___y_1382_);
lean_dec_ref(v___y_1381_);
lean_dec(v___y_1380_);
lean_dec_ref(v___y_1379_);
lean_dec(v___y_1378_);
return v_res_1384_;
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__1___closed__0(void){
_start:
{
lean_object* v___x_1386_; lean_object* v_dummy_1387_; 
v___x_1386_ = lean_box(0);
v_dummy_1387_ = l_Lean_Expr_sort___override(v___x_1386_);
return v_dummy_1387_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__1(lean_object* v_pre_1388_, lean_object* v_post_1389_, size_t v_sz_1390_, size_t v_i_1391_, lean_object* v_bs_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_){
_start:
{
uint8_t v___x_1399_; 
v___x_1399_ = lean_usize_dec_lt(v_i_1391_, v_sz_1390_);
if (v___x_1399_ == 0)
{
lean_object* v___x_1400_; 
lean_dec_ref(v_post_1389_);
lean_dec_ref(v_pre_1388_);
v___x_1400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1400_, 0, v_bs_1392_);
return v___x_1400_;
}
else
{
lean_object* v_v_1401_; lean_object* v___x_1402_; 
v_v_1401_ = lean_array_uget_borrowed(v_bs_1392_, v_i_1391_);
lean_inc(v_v_1401_);
lean_inc_ref(v_post_1389_);
lean_inc_ref(v_pre_1388_);
v___x_1402_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1388_, v_post_1389_, v_v_1401_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_);
if (lean_obj_tag(v___x_1402_) == 0)
{
lean_object* v_a_1403_; lean_object* v___x_1404_; lean_object* v_bs_x27_1405_; size_t v___x_1406_; size_t v___x_1407_; lean_object* v___x_1408_; 
v_a_1403_ = lean_ctor_get(v___x_1402_, 0);
lean_inc(v_a_1403_);
lean_dec_ref_known(v___x_1402_, 1);
v___x_1404_ = lean_unsigned_to_nat(0u);
v_bs_x27_1405_ = lean_array_uset(v_bs_1392_, v_i_1391_, v___x_1404_);
v___x_1406_ = ((size_t)1ULL);
v___x_1407_ = lean_usize_add(v_i_1391_, v___x_1406_);
v___x_1408_ = lean_array_uset(v_bs_x27_1405_, v_i_1391_, v_a_1403_);
v_i_1391_ = v___x_1407_;
v_bs_1392_ = v___x_1408_;
goto _start;
}
else
{
lean_object* v_a_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1417_; 
lean_dec_ref(v_bs_1392_);
lean_dec_ref(v_post_1389_);
lean_dec_ref(v_pre_1388_);
v_a_1410_ = lean_ctor_get(v___x_1402_, 0);
v_isSharedCheck_1417_ = !lean_is_exclusive(v___x_1402_);
if (v_isSharedCheck_1417_ == 0)
{
v___x_1412_ = v___x_1402_;
v_isShared_1413_ = v_isSharedCheck_1417_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_a_1410_);
lean_dec(v___x_1402_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1417_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v___x_1415_; 
if (v_isShared_1413_ == 0)
{
v___x_1415_ = v___x_1412_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v_a_1410_);
v___x_1415_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
return v___x_1415_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__4(lean_object* v_pre_1418_, lean_object* v_post_1419_, lean_object* v_x_1420_, lean_object* v_x_1421_, lean_object* v_x_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_){
_start:
{
if (lean_obj_tag(v_x_1420_) == 5)
{
lean_object* v_fn_1429_; lean_object* v_arg_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; 
v_fn_1429_ = lean_ctor_get(v_x_1420_, 0);
lean_inc_ref(v_fn_1429_);
v_arg_1430_ = lean_ctor_get(v_x_1420_, 1);
lean_inc_ref(v_arg_1430_);
lean_dec_ref_known(v_x_1420_, 2);
v___x_1431_ = lean_array_set(v_x_1421_, v_x_1422_, v_arg_1430_);
v___x_1432_ = lean_unsigned_to_nat(1u);
v___x_1433_ = lean_nat_sub(v_x_1422_, v___x_1432_);
lean_dec(v_x_1422_);
v_x_1420_ = v_fn_1429_;
v_x_1421_ = v___x_1431_;
v_x_1422_ = v___x_1433_;
goto _start;
}
else
{
lean_object* v___x_1435_; 
lean_dec(v_x_1422_);
lean_inc_ref(v_post_1419_);
lean_inc_ref(v_pre_1418_);
v___x_1435_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1418_, v_post_1419_, v_x_1420_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_);
if (lean_obj_tag(v___x_1435_) == 0)
{
lean_object* v_a_1436_; size_t v_sz_1437_; size_t v___x_1438_; lean_object* v___x_1439_; 
v_a_1436_ = lean_ctor_get(v___x_1435_, 0);
lean_inc(v_a_1436_);
lean_dec_ref_known(v___x_1435_, 1);
v_sz_1437_ = lean_array_size(v_x_1421_);
v___x_1438_ = ((size_t)0ULL);
lean_inc_ref(v_post_1419_);
lean_inc_ref(v_pre_1418_);
v___x_1439_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__1(v_pre_1418_, v_post_1419_, v_sz_1437_, v___x_1438_, v_x_1421_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_);
if (lean_obj_tag(v___x_1439_) == 0)
{
lean_object* v_a_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; 
v_a_1440_ = lean_ctor_get(v___x_1439_, 0);
lean_inc(v_a_1440_);
lean_dec_ref_known(v___x_1439_, 1);
v___x_1441_ = l_Lean_mkAppN(v_a_1436_, v_a_1440_);
lean_dec(v_a_1440_);
v___x_1442_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1418_, v_post_1419_, v___x_1441_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_);
return v___x_1442_;
}
else
{
lean_object* v_a_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1450_; 
lean_dec(v_a_1436_);
lean_dec_ref(v_post_1419_);
lean_dec_ref(v_pre_1418_);
v_a_1443_ = lean_ctor_get(v___x_1439_, 0);
v_isSharedCheck_1450_ = !lean_is_exclusive(v___x_1439_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1445_ = v___x_1439_;
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_a_1443_);
lean_dec(v___x_1439_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v___x_1448_; 
if (v_isShared_1446_ == 0)
{
v___x_1448_ = v___x_1445_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_a_1443_);
v___x_1448_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
return v___x_1448_;
}
}
}
}
else
{
lean_dec_ref(v_x_1421_);
lean_dec_ref(v_post_1419_);
lean_dec_ref(v_pre_1418_);
return v___x_1435_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__1(lean_object* v___x_1451_, lean_object* v_pre_1452_, lean_object* v_e_1453_, lean_object* v_post_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_){
_start:
{
lean_object* v___y_1462_; lean_object* v___y_1463_; lean_object* v___y_1464_; lean_object* v___y_1465_; uint8_t v___y_1466_; lean_object* v___y_1467_; lean_object* v___y_1468_; uint8_t v___y_1469_; lean_object* v___y_1479_; uint8_t v___y_1480_; lean_object* v___y_1481_; lean_object* v___y_1482_; lean_object* v___y_1483_; uint8_t v___y_1484_; uint8_t v___y_1492_; lean_object* v___y_1493_; lean_object* v___y_1494_; lean_object* v___y_1495_; lean_object* v___y_1496_; uint8_t v___y_1497_; lean_object* v___x_1504_; 
v___x_1504_ = l_Lean_Core_checkSystem(v___x_1451_, v___y_1458_, v___y_1459_);
if (lean_obj_tag(v___x_1504_) == 0)
{
lean_object* v___x_1505_; 
lean_dec_ref_known(v___x_1504_, 1);
lean_inc_ref(v_pre_1452_);
lean_inc(v___y_1459_);
lean_inc_ref(v___y_1458_);
lean_inc(v___y_1457_);
lean_inc_ref(v___y_1456_);
lean_inc_ref(v_e_1453_);
v___x_1505_ = lean_apply_6(v_pre_1452_, v_e_1453_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, lean_box(0));
if (lean_obj_tag(v___x_1505_) == 0)
{
lean_object* v_a_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1595_; 
v_a_1506_ = lean_ctor_get(v___x_1505_, 0);
v_isSharedCheck_1595_ = !lean_is_exclusive(v___x_1505_);
if (v_isSharedCheck_1595_ == 0)
{
v___x_1508_ = v___x_1505_;
v_isShared_1509_ = v_isSharedCheck_1595_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_a_1506_);
lean_dec(v___x_1505_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1595_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v___y_1511_; 
switch(lean_obj_tag(v_a_1506_))
{
case 0:
{
lean_object* v_e_1585_; lean_object* v___x_1587_; 
lean_dec_ref(v_post_1454_);
lean_dec_ref(v_e_1453_);
lean_dec_ref(v_pre_1452_);
v_e_1585_ = lean_ctor_get(v_a_1506_, 0);
lean_inc_ref(v_e_1585_);
lean_dec_ref_known(v_a_1506_, 1);
if (v_isShared_1509_ == 0)
{
lean_ctor_set(v___x_1508_, 0, v_e_1585_);
v___x_1587_ = v___x_1508_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_e_1585_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
return v___x_1587_;
}
}
case 1:
{
lean_object* v_e_1589_; lean_object* v___x_1590_; 
lean_del_object(v___x_1508_);
lean_dec_ref(v_e_1453_);
v_e_1589_ = lean_ctor_get(v_a_1506_, 0);
lean_inc_ref(v_e_1589_);
lean_dec_ref_known(v_a_1506_, 1);
lean_inc_ref(v_post_1454_);
lean_inc_ref(v_pre_1452_);
v___x_1590_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1452_, v_post_1454_, v_e_1589_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
if (lean_obj_tag(v___x_1590_) == 0)
{
lean_object* v_a_1591_; lean_object* v___x_1592_; 
v_a_1591_ = lean_ctor_get(v___x_1590_, 0);
lean_inc(v_a_1591_);
lean_dec_ref_known(v___x_1590_, 1);
v___x_1592_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1452_, v_post_1454_, v_a_1591_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
return v___x_1592_;
}
else
{
lean_dec_ref(v_post_1454_);
lean_dec_ref(v_pre_1452_);
return v___x_1590_;
}
}
default: 
{
lean_object* v_e_x3f_1593_; 
lean_del_object(v___x_1508_);
v_e_x3f_1593_ = lean_ctor_get(v_a_1506_, 0);
lean_inc(v_e_x3f_1593_);
lean_dec_ref_known(v_a_1506_, 1);
if (lean_obj_tag(v_e_x3f_1593_) == 0)
{
v___y_1511_ = v_e_1453_;
goto v___jp_1510_;
}
else
{
lean_object* v_val_1594_; 
lean_dec_ref(v_e_1453_);
v_val_1594_ = lean_ctor_get(v_e_x3f_1593_, 0);
lean_inc(v_val_1594_);
lean_dec_ref_known(v_e_x3f_1593_, 1);
v___y_1511_ = v_val_1594_;
goto v___jp_1510_;
}
}
}
v___jp_1510_:
{
switch(lean_obj_tag(v___y_1511_))
{
case 7:
{
lean_object* v_binderName_1512_; lean_object* v_binderType_1513_; lean_object* v_body_1514_; uint8_t v_binderInfo_1515_; lean_object* v___x_1516_; 
v_binderName_1512_ = lean_ctor_get(v___y_1511_, 0);
lean_inc(v_binderName_1512_);
v_binderType_1513_ = lean_ctor_get(v___y_1511_, 1);
v_body_1514_ = lean_ctor_get(v___y_1511_, 2);
v_binderInfo_1515_ = lean_ctor_get_uint8(v___y_1511_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1513_);
lean_inc_ref(v_post_1454_);
lean_inc_ref(v_pre_1452_);
v___x_1516_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1452_, v_post_1454_, v_binderType_1513_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
if (lean_obj_tag(v___x_1516_) == 0)
{
lean_object* v_a_1517_; lean_object* v___x_1518_; 
v_a_1517_ = lean_ctor_get(v___x_1516_, 0);
lean_inc(v_a_1517_);
lean_dec_ref_known(v___x_1516_, 1);
lean_inc_ref(v_body_1514_);
lean_inc_ref(v_post_1454_);
lean_inc_ref(v_pre_1452_);
v___x_1518_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1452_, v_post_1454_, v_body_1514_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
if (lean_obj_tag(v___x_1518_) == 0)
{
lean_object* v_a_1519_; size_t v___x_1520_; size_t v___x_1521_; uint8_t v___x_1522_; 
v_a_1519_ = lean_ctor_get(v___x_1518_, 0);
lean_inc(v_a_1519_);
lean_dec_ref_known(v___x_1518_, 1);
v___x_1520_ = lean_ptr_addr(v_binderType_1513_);
v___x_1521_ = lean_ptr_addr(v_a_1517_);
v___x_1522_ = lean_usize_dec_eq(v___x_1520_, v___x_1521_);
if (v___x_1522_ == 0)
{
v___y_1492_ = v_binderInfo_1515_;
v___y_1493_ = v_binderName_1512_;
v___y_1494_ = v_a_1519_;
v___y_1495_ = v___y_1511_;
v___y_1496_ = v_a_1517_;
v___y_1497_ = v___x_1522_;
goto v___jp_1491_;
}
else
{
size_t v___x_1523_; size_t v___x_1524_; uint8_t v___x_1525_; 
v___x_1523_ = lean_ptr_addr(v_body_1514_);
v___x_1524_ = lean_ptr_addr(v_a_1519_);
v___x_1525_ = lean_usize_dec_eq(v___x_1523_, v___x_1524_);
v___y_1492_ = v_binderInfo_1515_;
v___y_1493_ = v_binderName_1512_;
v___y_1494_ = v_a_1519_;
v___y_1495_ = v___y_1511_;
v___y_1496_ = v_a_1517_;
v___y_1497_ = v___x_1525_;
goto v___jp_1491_;
}
}
else
{
lean_dec(v_a_1517_);
lean_dec(v_binderName_1512_);
lean_dec_ref_known(v___y_1511_, 3);
lean_dec_ref(v_post_1454_);
lean_dec_ref(v_pre_1452_);
return v___x_1518_;
}
}
else
{
lean_dec(v_binderName_1512_);
lean_dec_ref_known(v___y_1511_, 3);
lean_dec_ref(v_post_1454_);
lean_dec_ref(v_pre_1452_);
return v___x_1516_;
}
}
case 6:
{
lean_object* v_binderName_1526_; lean_object* v_binderType_1527_; lean_object* v_body_1528_; uint8_t v_binderInfo_1529_; lean_object* v___x_1530_; 
v_binderName_1526_ = lean_ctor_get(v___y_1511_, 0);
lean_inc(v_binderName_1526_);
v_binderType_1527_ = lean_ctor_get(v___y_1511_, 1);
v_body_1528_ = lean_ctor_get(v___y_1511_, 2);
v_binderInfo_1529_ = lean_ctor_get_uint8(v___y_1511_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1527_);
lean_inc_ref(v_post_1454_);
lean_inc_ref(v_pre_1452_);
v___x_1530_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1452_, v_post_1454_, v_binderType_1527_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
if (lean_obj_tag(v___x_1530_) == 0)
{
lean_object* v_a_1531_; lean_object* v___x_1532_; 
v_a_1531_ = lean_ctor_get(v___x_1530_, 0);
lean_inc(v_a_1531_);
lean_dec_ref_known(v___x_1530_, 1);
lean_inc_ref(v_body_1528_);
lean_inc_ref(v_post_1454_);
lean_inc_ref(v_pre_1452_);
v___x_1532_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1452_, v_post_1454_, v_body_1528_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
if (lean_obj_tag(v___x_1532_) == 0)
{
lean_object* v_a_1533_; size_t v___x_1534_; size_t v___x_1535_; uint8_t v___x_1536_; 
v_a_1533_ = lean_ctor_get(v___x_1532_, 0);
lean_inc(v_a_1533_);
lean_dec_ref_known(v___x_1532_, 1);
v___x_1534_ = lean_ptr_addr(v_binderType_1527_);
v___x_1535_ = lean_ptr_addr(v_a_1531_);
v___x_1536_ = lean_usize_dec_eq(v___x_1534_, v___x_1535_);
if (v___x_1536_ == 0)
{
v___y_1479_ = v_a_1533_;
v___y_1480_ = v_binderInfo_1529_;
v___y_1481_ = v_a_1531_;
v___y_1482_ = v_binderName_1526_;
v___y_1483_ = v___y_1511_;
v___y_1484_ = v___x_1536_;
goto v___jp_1478_;
}
else
{
size_t v___x_1537_; size_t v___x_1538_; uint8_t v___x_1539_; 
v___x_1537_ = lean_ptr_addr(v_body_1528_);
v___x_1538_ = lean_ptr_addr(v_a_1533_);
v___x_1539_ = lean_usize_dec_eq(v___x_1537_, v___x_1538_);
v___y_1479_ = v_a_1533_;
v___y_1480_ = v_binderInfo_1529_;
v___y_1481_ = v_a_1531_;
v___y_1482_ = v_binderName_1526_;
v___y_1483_ = v___y_1511_;
v___y_1484_ = v___x_1539_;
goto v___jp_1478_;
}
}
else
{
lean_dec(v_a_1531_);
lean_dec(v_binderName_1526_);
lean_dec_ref_known(v___y_1511_, 3);
lean_dec_ref(v_post_1454_);
lean_dec_ref(v_pre_1452_);
return v___x_1532_;
}
}
else
{
lean_dec(v_binderName_1526_);
lean_dec_ref_known(v___y_1511_, 3);
lean_dec_ref(v_post_1454_);
lean_dec_ref(v_pre_1452_);
return v___x_1530_;
}
}
case 8:
{
lean_object* v_declName_1540_; lean_object* v_type_1541_; lean_object* v_value_1542_; lean_object* v_body_1543_; uint8_t v_nondep_1544_; lean_object* v___x_1545_; 
v_declName_1540_ = lean_ctor_get(v___y_1511_, 0);
lean_inc(v_declName_1540_);
v_type_1541_ = lean_ctor_get(v___y_1511_, 1);
v_value_1542_ = lean_ctor_get(v___y_1511_, 2);
v_body_1543_ = lean_ctor_get(v___y_1511_, 3);
lean_inc_ref(v_body_1543_);
v_nondep_1544_ = lean_ctor_get_uint8(v___y_1511_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_1541_);
lean_inc_ref(v_post_1454_);
lean_inc_ref(v_pre_1452_);
v___x_1545_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1452_, v_post_1454_, v_type_1541_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v_a_1546_; lean_object* v___x_1547_; 
v_a_1546_ = lean_ctor_get(v___x_1545_, 0);
lean_inc(v_a_1546_);
lean_dec_ref_known(v___x_1545_, 1);
lean_inc_ref(v_value_1542_);
lean_inc_ref(v_post_1454_);
lean_inc_ref(v_pre_1452_);
v___x_1547_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1452_, v_post_1454_, v_value_1542_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_object* v_a_1548_; lean_object* v___x_1549_; 
v_a_1548_ = lean_ctor_get(v___x_1547_, 0);
lean_inc(v_a_1548_);
lean_dec_ref_known(v___x_1547_, 1);
lean_inc_ref(v_body_1543_);
lean_inc_ref(v_post_1454_);
lean_inc_ref(v_pre_1452_);
v___x_1549_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1452_, v_post_1454_, v_body_1543_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_object* v_a_1550_; size_t v___x_1551_; size_t v___x_1552_; uint8_t v___x_1553_; 
v_a_1550_ = lean_ctor_get(v___x_1549_, 0);
lean_inc(v_a_1550_);
lean_dec_ref_known(v___x_1549_, 1);
v___x_1551_ = lean_ptr_addr(v_type_1541_);
v___x_1552_ = lean_ptr_addr(v_a_1546_);
v___x_1553_ = lean_usize_dec_eq(v___x_1551_, v___x_1552_);
if (v___x_1553_ == 0)
{
v___y_1462_ = v_body_1543_;
v___y_1463_ = v_declName_1540_;
v___y_1464_ = v_a_1550_;
v___y_1465_ = v_a_1548_;
v___y_1466_ = v_nondep_1544_;
v___y_1467_ = v___y_1511_;
v___y_1468_ = v_a_1546_;
v___y_1469_ = v___x_1553_;
goto v___jp_1461_;
}
else
{
size_t v___x_1554_; size_t v___x_1555_; uint8_t v___x_1556_; 
v___x_1554_ = lean_ptr_addr(v_value_1542_);
v___x_1555_ = lean_ptr_addr(v_a_1548_);
v___x_1556_ = lean_usize_dec_eq(v___x_1554_, v___x_1555_);
v___y_1462_ = v_body_1543_;
v___y_1463_ = v_declName_1540_;
v___y_1464_ = v_a_1550_;
v___y_1465_ = v_a_1548_;
v___y_1466_ = v_nondep_1544_;
v___y_1467_ = v___y_1511_;
v___y_1468_ = v_a_1546_;
v___y_1469_ = v___x_1556_;
goto v___jp_1461_;
}
}
else
{
lean_dec(v_a_1548_);
lean_dec(v_a_1546_);
lean_dec_ref(v_body_1543_);
lean_dec_ref_known(v___y_1511_, 4);
lean_dec(v_declName_1540_);
lean_dec_ref(v_post_1454_);
lean_dec_ref(v_pre_1452_);
return v___x_1549_;
}
}
else
{
lean_dec(v_a_1546_);
lean_dec_ref(v_body_1543_);
lean_dec_ref_known(v___y_1511_, 4);
lean_dec(v_declName_1540_);
lean_dec_ref(v_post_1454_);
lean_dec_ref(v_pre_1452_);
return v___x_1547_;
}
}
else
{
lean_dec_ref(v_body_1543_);
lean_dec(v_declName_1540_);
lean_dec_ref_known(v___y_1511_, 4);
lean_dec_ref(v_post_1454_);
lean_dec_ref(v_pre_1452_);
return v___x_1545_;
}
}
case 5:
{
lean_object* v_dummy_1557_; lean_object* v_nargs_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; 
v_dummy_1557_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__1___closed__0);
v_nargs_1558_ = l_Lean_Expr_getAppNumArgs(v___y_1511_);
lean_inc(v_nargs_1558_);
v___x_1559_ = lean_mk_array(v_nargs_1558_, v_dummy_1557_);
v___x_1560_ = lean_unsigned_to_nat(1u);
v___x_1561_ = lean_nat_sub(v_nargs_1558_, v___x_1560_);
lean_dec(v_nargs_1558_);
v___x_1562_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__4(v_pre_1452_, v_post_1454_, v___y_1511_, v___x_1559_, v___x_1561_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
return v___x_1562_;
}
case 10:
{
lean_object* v_data_1563_; lean_object* v_expr_1564_; lean_object* v___x_1565_; 
v_data_1563_ = lean_ctor_get(v___y_1511_, 0);
v_expr_1564_ = lean_ctor_get(v___y_1511_, 1);
lean_inc_ref(v_expr_1564_);
lean_inc_ref(v_post_1454_);
lean_inc_ref(v_pre_1452_);
v___x_1565_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1452_, v_post_1454_, v_expr_1564_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
if (lean_obj_tag(v___x_1565_) == 0)
{
lean_object* v_a_1566_; size_t v___x_1567_; size_t v___x_1568_; uint8_t v___x_1569_; 
v_a_1566_ = lean_ctor_get(v___x_1565_, 0);
lean_inc(v_a_1566_);
lean_dec_ref_known(v___x_1565_, 1);
v___x_1567_ = lean_ptr_addr(v_expr_1564_);
v___x_1568_ = lean_ptr_addr(v_a_1566_);
v___x_1569_ = lean_usize_dec_eq(v___x_1567_, v___x_1568_);
if (v___x_1569_ == 0)
{
lean_object* v___x_1570_; lean_object* v___x_1571_; 
lean_inc(v_data_1563_);
lean_dec_ref_known(v___y_1511_, 2);
v___x_1570_ = l_Lean_Expr_mdata___override(v_data_1563_, v_a_1566_);
v___x_1571_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1452_, v_post_1454_, v___x_1570_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
return v___x_1571_;
}
else
{
lean_object* v___x_1572_; 
lean_dec(v_a_1566_);
v___x_1572_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1452_, v_post_1454_, v___y_1511_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
return v___x_1572_;
}
}
else
{
lean_dec_ref_known(v___y_1511_, 2);
lean_dec_ref(v_post_1454_);
lean_dec_ref(v_pre_1452_);
return v___x_1565_;
}
}
case 11:
{
lean_object* v_typeName_1573_; lean_object* v_idx_1574_; lean_object* v_struct_1575_; lean_object* v___x_1576_; 
v_typeName_1573_ = lean_ctor_get(v___y_1511_, 0);
v_idx_1574_ = lean_ctor_get(v___y_1511_, 1);
v_struct_1575_ = lean_ctor_get(v___y_1511_, 2);
lean_inc_ref(v_struct_1575_);
lean_inc_ref(v_post_1454_);
lean_inc_ref(v_pre_1452_);
v___x_1576_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1452_, v_post_1454_, v_struct_1575_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
if (lean_obj_tag(v___x_1576_) == 0)
{
lean_object* v_a_1577_; size_t v___x_1578_; size_t v___x_1579_; uint8_t v___x_1580_; 
v_a_1577_ = lean_ctor_get(v___x_1576_, 0);
lean_inc(v_a_1577_);
lean_dec_ref_known(v___x_1576_, 1);
v___x_1578_ = lean_ptr_addr(v_struct_1575_);
v___x_1579_ = lean_ptr_addr(v_a_1577_);
v___x_1580_ = lean_usize_dec_eq(v___x_1578_, v___x_1579_);
if (v___x_1580_ == 0)
{
lean_object* v___x_1581_; lean_object* v___x_1582_; 
lean_inc(v_idx_1574_);
lean_inc(v_typeName_1573_);
lean_dec_ref_known(v___y_1511_, 3);
v___x_1581_ = l_Lean_Expr_proj___override(v_typeName_1573_, v_idx_1574_, v_a_1577_);
v___x_1582_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1452_, v_post_1454_, v___x_1581_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
return v___x_1582_;
}
else
{
lean_object* v___x_1583_; 
lean_dec(v_a_1577_);
v___x_1583_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1452_, v_post_1454_, v___y_1511_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
return v___x_1583_;
}
}
else
{
lean_dec_ref_known(v___y_1511_, 3);
lean_dec_ref(v_post_1454_);
lean_dec_ref(v_pre_1452_);
return v___x_1576_;
}
}
default: 
{
lean_object* v___x_1584_; 
v___x_1584_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1452_, v_post_1454_, v___y_1511_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
return v___x_1584_;
}
}
}
}
}
else
{
lean_object* v_a_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1603_; 
lean_dec_ref(v_post_1454_);
lean_dec_ref(v_e_1453_);
lean_dec_ref(v_pre_1452_);
v_a_1596_ = lean_ctor_get(v___x_1505_, 0);
v_isSharedCheck_1603_ = !lean_is_exclusive(v___x_1505_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1598_ = v___x_1505_;
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_a_1596_);
lean_dec(v___x_1505_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v___x_1601_; 
if (v_isShared_1599_ == 0)
{
v___x_1601_ = v___x_1598_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v_a_1596_);
v___x_1601_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
return v___x_1601_;
}
}
}
}
else
{
lean_object* v_a_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1611_; 
lean_dec_ref(v_post_1454_);
lean_dec_ref(v_e_1453_);
lean_dec_ref(v_pre_1452_);
v_a_1604_ = lean_ctor_get(v___x_1504_, 0);
v_isSharedCheck_1611_ = !lean_is_exclusive(v___x_1504_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1606_ = v___x_1504_;
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_a_1604_);
lean_dec(v___x_1504_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v___x_1609_; 
if (v_isShared_1607_ == 0)
{
v___x_1609_ = v___x_1606_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_a_1604_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
return v___x_1609_;
}
}
}
v___jp_1461_:
{
if (v___y_1469_ == 0)
{
lean_object* v___x_1470_; lean_object* v___x_1471_; 
lean_dec_ref(v___y_1467_);
lean_dec_ref(v___y_1462_);
v___x_1470_ = l_Lean_Expr_letE___override(v___y_1463_, v___y_1468_, v___y_1465_, v___y_1464_, v___y_1466_);
v___x_1471_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1452_, v_post_1454_, v___x_1470_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
return v___x_1471_;
}
else
{
size_t v___x_1472_; size_t v___x_1473_; uint8_t v___x_1474_; 
v___x_1472_ = lean_ptr_addr(v___y_1462_);
lean_dec_ref(v___y_1462_);
v___x_1473_ = lean_ptr_addr(v___y_1464_);
v___x_1474_ = lean_usize_dec_eq(v___x_1472_, v___x_1473_);
if (v___x_1474_ == 0)
{
lean_object* v___x_1475_; lean_object* v___x_1476_; 
lean_dec_ref(v___y_1467_);
v___x_1475_ = l_Lean_Expr_letE___override(v___y_1463_, v___y_1468_, v___y_1465_, v___y_1464_, v___y_1466_);
v___x_1476_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1452_, v_post_1454_, v___x_1475_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
return v___x_1476_;
}
else
{
lean_object* v___x_1477_; 
lean_dec_ref(v___y_1468_);
lean_dec_ref(v___y_1465_);
lean_dec_ref(v___y_1464_);
lean_dec(v___y_1463_);
v___x_1477_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1452_, v_post_1454_, v___y_1467_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
return v___x_1477_;
}
}
}
v___jp_1478_:
{
if (v___y_1484_ == 0)
{
lean_object* v___x_1485_; lean_object* v___x_1486_; 
lean_dec_ref(v___y_1483_);
v___x_1485_ = l_Lean_Expr_lam___override(v___y_1482_, v___y_1481_, v___y_1479_, v___y_1480_);
v___x_1486_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1452_, v_post_1454_, v___x_1485_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
return v___x_1486_;
}
else
{
uint8_t v___x_1487_; 
v___x_1487_ = l_Lean_instBEqBinderInfo_beq(v___y_1480_, v___y_1480_);
if (v___x_1487_ == 0)
{
lean_object* v___x_1488_; lean_object* v___x_1489_; 
lean_dec_ref(v___y_1483_);
v___x_1488_ = l_Lean_Expr_lam___override(v___y_1482_, v___y_1481_, v___y_1479_, v___y_1480_);
v___x_1489_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1452_, v_post_1454_, v___x_1488_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
return v___x_1489_;
}
else
{
lean_object* v___x_1490_; 
lean_dec(v___y_1482_);
lean_dec_ref(v___y_1481_);
lean_dec_ref(v___y_1479_);
v___x_1490_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1452_, v_post_1454_, v___y_1483_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
return v___x_1490_;
}
}
}
v___jp_1491_:
{
if (v___y_1497_ == 0)
{
lean_object* v___x_1498_; lean_object* v___x_1499_; 
lean_dec_ref(v___y_1495_);
v___x_1498_ = l_Lean_Expr_forallE___override(v___y_1493_, v___y_1496_, v___y_1494_, v___y_1492_);
v___x_1499_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1452_, v_post_1454_, v___x_1498_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
return v___x_1499_;
}
else
{
uint8_t v___x_1500_; 
v___x_1500_ = l_Lean_instBEqBinderInfo_beq(v___y_1492_, v___y_1492_);
if (v___x_1500_ == 0)
{
lean_object* v___x_1501_; lean_object* v___x_1502_; 
lean_dec_ref(v___y_1495_);
v___x_1501_ = l_Lean_Expr_forallE___override(v___y_1493_, v___y_1496_, v___y_1494_, v___y_1492_);
v___x_1502_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1452_, v_post_1454_, v___x_1501_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
return v___x_1502_;
}
else
{
lean_object* v___x_1503_; 
lean_dec_ref(v___y_1496_);
lean_dec_ref(v___y_1494_);
lean_dec(v___y_1493_);
v___x_1503_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1452_, v_post_1454_, v___y_1495_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
return v___x_1503_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__1___boxed(lean_object* v___x_1612_, lean_object* v_pre_1613_, lean_object* v_e_1614_, lean_object* v_post_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_){
_start:
{
lean_object* v_res_1622_; 
v_res_1622_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__1(v___x_1612_, v_pre_1613_, v_e_1614_, v_post_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_);
lean_dec(v___y_1620_);
lean_dec_ref(v___y_1619_);
lean_dec(v___y_1618_);
lean_dec_ref(v___y_1617_);
lean_dec(v___y_1616_);
return v_res_1622_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(lean_object* v_pre_1623_, lean_object* v_post_1624_, lean_object* v_e_1625_, lean_object* v_a_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_){
_start:
{
lean_object* v___x_1632_; lean_object* v___x_1633_; 
lean_inc(v_a_1626_);
v___x_1632_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1632_, 0, lean_box(0));
lean_closure_set(v___x_1632_, 1, lean_box(0));
lean_closure_set(v___x_1632_, 2, v_a_1626_);
v___x_1633_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__0(lean_box(0), v___x_1632_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_);
if (lean_obj_tag(v___x_1633_) == 0)
{
lean_object* v_a_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1665_; 
v_a_1634_ = lean_ctor_get(v___x_1633_, 0);
v_isSharedCheck_1665_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1636_ = v___x_1633_;
v_isShared_1637_ = v_isSharedCheck_1665_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_a_1634_);
lean_dec(v___x_1633_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1665_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
lean_object* v___x_1638_; 
v___x_1638_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3___redArg(v_a_1634_, v_e_1625_);
lean_dec(v_a_1634_);
if (lean_obj_tag(v___x_1638_) == 0)
{
lean_object* v___x_1639_; lean_object* v___f_1640_; lean_object* v___x_1641_; 
lean_del_object(v___x_1636_);
v___x_1639_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___closed__0));
lean_inc_ref(v_e_1625_);
v___f_1640_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__1___boxed), 10, 4);
lean_closure_set(v___f_1640_, 0, v___x_1639_);
lean_closure_set(v___f_1640_, 1, v_pre_1623_);
lean_closure_set(v___f_1640_, 2, v_e_1625_);
lean_closure_set(v___f_1640_, 3, v_post_1624_);
v___x_1641_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5___redArg(v___f_1640_, v_a_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_);
if (lean_obj_tag(v___x_1641_) == 0)
{
lean_object* v_a_1642_; lean_object* v___f_1643_; lean_object* v___x_1644_; 
v_a_1642_ = lean_ctor_get(v___x_1641_, 0);
lean_inc_n(v_a_1642_, 2);
lean_dec_ref_known(v___x_1641_, 1);
lean_inc(v_a_1626_);
v___f_1643_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1643_, 0, v_a_1626_);
lean_closure_set(v___f_1643_, 1, v_e_1625_);
lean_closure_set(v___f_1643_, 2, v_a_1642_);
v___x_1644_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__0(lean_box(0), v___f_1643_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_);
if (lean_obj_tag(v___x_1644_) == 0)
{
lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1651_; 
v_isSharedCheck_1651_ = !lean_is_exclusive(v___x_1644_);
if (v_isSharedCheck_1651_ == 0)
{
lean_object* v_unused_1652_; 
v_unused_1652_ = lean_ctor_get(v___x_1644_, 0);
lean_dec(v_unused_1652_);
v___x_1646_ = v___x_1644_;
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
else
{
lean_dec(v___x_1644_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
lean_object* v___x_1649_; 
if (v_isShared_1647_ == 0)
{
lean_ctor_set(v___x_1646_, 0, v_a_1642_);
v___x_1649_ = v___x_1646_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v_a_1642_);
v___x_1649_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
return v___x_1649_;
}
}
}
else
{
lean_object* v_a_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1660_; 
lean_dec(v_a_1642_);
v_a_1653_ = lean_ctor_get(v___x_1644_, 0);
v_isSharedCheck_1660_ = !lean_is_exclusive(v___x_1644_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1655_ = v___x_1644_;
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_a_1653_);
lean_dec(v___x_1644_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1658_; 
if (v_isShared_1656_ == 0)
{
v___x_1658_ = v___x_1655_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v_a_1653_);
v___x_1658_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
return v___x_1658_;
}
}
}
}
else
{
lean_dec_ref(v_e_1625_);
return v___x_1641_;
}
}
else
{
lean_object* v_val_1661_; lean_object* v___x_1663_; 
lean_dec_ref(v_e_1625_);
lean_dec_ref(v_post_1624_);
lean_dec_ref(v_pre_1623_);
v_val_1661_ = lean_ctor_get(v___x_1638_, 0);
lean_inc(v_val_1661_);
lean_dec_ref_known(v___x_1638_, 1);
if (v_isShared_1637_ == 0)
{
lean_ctor_set(v___x_1636_, 0, v_val_1661_);
v___x_1663_ = v___x_1636_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v_val_1661_);
v___x_1663_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
return v___x_1663_;
}
}
}
}
else
{
lean_object* v_a_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1673_; 
lean_dec_ref(v_e_1625_);
lean_dec_ref(v_post_1624_);
lean_dec_ref(v_pre_1623_);
v_a_1666_ = lean_ctor_get(v___x_1633_, 0);
v_isSharedCheck_1673_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1673_ == 0)
{
v___x_1668_ = v___x_1633_;
v_isShared_1669_ = v_isSharedCheck_1673_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_a_1666_);
lean_dec(v___x_1633_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(lean_object* v_pre_1674_, lean_object* v_post_1675_, lean_object* v_e_1676_, lean_object* v_a_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_){
_start:
{
lean_object* v___x_1683_; 
lean_inc_ref(v_post_1675_);
lean_inc(v___y_1681_);
lean_inc_ref(v___y_1680_);
lean_inc(v___y_1679_);
lean_inc_ref(v___y_1678_);
lean_inc_ref(v_e_1676_);
v___x_1683_ = lean_apply_6(v_post_1675_, v_e_1676_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, lean_box(0));
if (lean_obj_tag(v___x_1683_) == 0)
{
lean_object* v_a_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1702_; 
v_a_1684_ = lean_ctor_get(v___x_1683_, 0);
v_isSharedCheck_1702_ = !lean_is_exclusive(v___x_1683_);
if (v_isSharedCheck_1702_ == 0)
{
v___x_1686_ = v___x_1683_;
v_isShared_1687_ = v_isSharedCheck_1702_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_a_1684_);
lean_dec(v___x_1683_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1702_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
switch(lean_obj_tag(v_a_1684_))
{
case 0:
{
lean_object* v_e_1688_; lean_object* v___x_1690_; 
lean_dec_ref(v_e_1676_);
lean_dec_ref(v_post_1675_);
lean_dec_ref(v_pre_1674_);
v_e_1688_ = lean_ctor_get(v_a_1684_, 0);
lean_inc_ref(v_e_1688_);
lean_dec_ref_known(v_a_1684_, 1);
if (v_isShared_1687_ == 0)
{
lean_ctor_set(v___x_1686_, 0, v_e_1688_);
v___x_1690_ = v___x_1686_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v_e_1688_);
v___x_1690_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
return v___x_1690_;
}
}
case 1:
{
lean_object* v_e_1692_; lean_object* v___x_1693_; 
lean_del_object(v___x_1686_);
lean_dec_ref(v_e_1676_);
v_e_1692_ = lean_ctor_get(v_a_1684_, 0);
lean_inc_ref(v_e_1692_);
lean_dec_ref_known(v_a_1684_, 1);
v___x_1693_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1674_, v_post_1675_, v_e_1692_, v_a_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_);
return v___x_1693_;
}
default: 
{
lean_object* v_e_x3f_1694_; 
lean_dec_ref(v_post_1675_);
lean_dec_ref(v_pre_1674_);
v_e_x3f_1694_ = lean_ctor_get(v_a_1684_, 0);
lean_inc(v_e_x3f_1694_);
lean_dec_ref_known(v_a_1684_, 1);
if (lean_obj_tag(v_e_x3f_1694_) == 0)
{
lean_object* v___x_1696_; 
if (v_isShared_1687_ == 0)
{
lean_ctor_set(v___x_1686_, 0, v_e_1676_);
v___x_1696_ = v___x_1686_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v_e_1676_);
v___x_1696_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
return v___x_1696_;
}
}
else
{
lean_object* v_val_1698_; lean_object* v___x_1700_; 
lean_dec_ref(v_e_1676_);
v_val_1698_ = lean_ctor_get(v_e_x3f_1694_, 0);
lean_inc(v_val_1698_);
lean_dec_ref_known(v_e_x3f_1694_, 1);
if (v_isShared_1687_ == 0)
{
lean_ctor_set(v___x_1686_, 0, v_val_1698_);
v___x_1700_ = v___x_1686_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v_val_1698_);
v___x_1700_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
return v___x_1700_;
}
}
}
}
}
}
else
{
lean_object* v_a_1703_; lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1710_; 
lean_dec_ref(v_e_1676_);
lean_dec_ref(v_post_1675_);
lean_dec_ref(v_pre_1674_);
v_a_1703_ = lean_ctor_get(v___x_1683_, 0);
v_isSharedCheck_1710_ = !lean_is_exclusive(v___x_1683_);
if (v_isSharedCheck_1710_ == 0)
{
v___x_1705_ = v___x_1683_;
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
else
{
lean_inc(v_a_1703_);
lean_dec(v___x_1683_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v___x_1708_; 
if (v_isShared_1706_ == 0)
{
v___x_1708_ = v___x_1705_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v_a_1703_);
v___x_1708_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
return v___x_1708_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_1711_, lean_object* v_post_1712_, lean_object* v_e_1713_, lean_object* v_a_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_){
_start:
{
lean_object* v_res_1720_; 
v_res_1720_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1711_, v_post_1712_, v_e_1713_, v_a_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_);
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1717_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
lean_dec(v_a_1714_);
return v_res_1720_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_1721_, lean_object* v_post_1722_, lean_object* v_sz_1723_, lean_object* v_i_1724_, lean_object* v_bs_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_){
_start:
{
size_t v_sz_boxed_1732_; size_t v_i_boxed_1733_; lean_object* v_res_1734_; 
v_sz_boxed_1732_ = lean_unbox_usize(v_sz_1723_);
lean_dec(v_sz_1723_);
v_i_boxed_1733_ = lean_unbox_usize(v_i_1724_);
lean_dec(v_i_1724_);
v_res_1734_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__1(v_pre_1721_, v_post_1722_, v_sz_boxed_1732_, v_i_boxed_1733_, v_bs_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_);
lean_dec(v___y_1730_);
lean_dec_ref(v___y_1729_);
lean_dec(v___y_1728_);
lean_dec_ref(v___y_1727_);
lean_dec(v___y_1726_);
return v_res_1734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__4___boxed(lean_object* v_pre_1735_, lean_object* v_post_1736_, lean_object* v_x_1737_, lean_object* v_x_1738_, lean_object* v_x_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_){
_start:
{
lean_object* v_res_1746_; 
v_res_1746_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__4(v_pre_1735_, v_post_1736_, v_x_1737_, v_x_1738_, v_x_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_);
lean_dec(v___y_1744_);
lean_dec_ref(v___y_1743_);
lean_dec(v___y_1742_);
lean_dec_ref(v___y_1741_);
lean_dec(v___y_1740_);
return v_res_1746_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___boxed(lean_object* v_pre_1747_, lean_object* v_post_1748_, lean_object* v_e_1749_, lean_object* v_a_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_){
_start:
{
lean_object* v_res_1756_; 
v_res_1756_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1747_, v_post_1748_, v_e_1749_, v_a_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_);
lean_dec(v___y_1754_);
lean_dec_ref(v___y_1753_);
lean_dec(v___y_1752_);
lean_dec_ref(v___y_1751_);
lean_dec(v_a_1750_);
return v_res_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___lam__0(lean_object* v_00_u03b1_1757_, lean_object* v_x_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_){
_start:
{
lean_object* v___x_1764_; lean_object* v___x_1765_; 
v___x_1764_ = lean_apply_1(v_x_1758_, lean_box(0));
v___x_1765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1765_, 0, v___x_1764_);
return v___x_1765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___lam__0___boxed(lean_object* v_00_u03b1_1766_, lean_object* v_x_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_){
_start:
{
lean_object* v_res_1773_; 
v_res_1773_ = l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___lam__0(v_00_u03b1_1766_, v_x_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_);
lean_dec(v___y_1771_);
lean_dec_ref(v___y_1770_);
lean_dec(v___y_1769_);
lean_dec_ref(v___y_1768_);
return v_res_1773_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; 
v___x_1774_ = lean_box(0);
v___x_1775_ = lean_unsigned_to_nat(16u);
v___x_1776_ = lean_mk_array(v___x_1775_, v___x_1774_);
return v___x_1776_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___x_1777_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__0, &l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__0_once, _init_l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__0);
v___x_1778_ = lean_unsigned_to_nat(0u);
v___x_1779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1779_, 0, v___x_1778_);
lean_ctor_set(v___x_1779_, 1, v___x_1777_);
return v___x_1779_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1780_; lean_object* v___x_1781_; 
v___x_1780_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__1, &l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__1_once, _init_l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__1);
v___x_1781_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1781_, 0, lean_box(0));
lean_closure_set(v___x_1781_, 1, lean_box(0));
lean_closure_set(v___x_1781_, 2, v___x_1780_);
return v___x_1781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0(lean_object* v_input_1782_, lean_object* v_pre_1783_, lean_object* v_post_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_){
_start:
{
lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v_a_1792_; lean_object* v___x_1793_; 
v___x_1790_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__2, &l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__2_once, _init_l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__2);
v___x_1791_ = l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___lam__0(lean_box(0), v___x_1790_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_);
v_a_1792_ = lean_ctor_get(v___x_1791_, 0);
lean_inc(v_a_1792_);
lean_dec_ref(v___x_1791_);
v___x_1793_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1783_, v_post_1784_, v_input_1782_, v_a_1792_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_);
if (lean_obj_tag(v___x_1793_) == 0)
{
lean_object* v_a_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1803_; 
v_a_1794_ = lean_ctor_get(v___x_1793_, 0);
lean_inc(v_a_1794_);
lean_dec_ref_known(v___x_1793_, 1);
v___x_1795_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1795_, 0, lean_box(0));
lean_closure_set(v___x_1795_, 1, lean_box(0));
lean_closure_set(v___x_1795_, 2, v_a_1792_);
v___x_1796_ = l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___lam__0(lean_box(0), v___x_1795_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_);
v_isSharedCheck_1803_ = !lean_is_exclusive(v___x_1796_);
if (v_isSharedCheck_1803_ == 0)
{
lean_object* v_unused_1804_; 
v_unused_1804_ = lean_ctor_get(v___x_1796_, 0);
lean_dec(v_unused_1804_);
v___x_1798_ = v___x_1796_;
v_isShared_1799_ = v_isSharedCheck_1803_;
goto v_resetjp_1797_;
}
else
{
lean_dec(v___x_1796_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1803_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
lean_object* v___x_1801_; 
if (v_isShared_1799_ == 0)
{
lean_ctor_set(v___x_1798_, 0, v_a_1794_);
v___x_1801_ = v___x_1798_;
goto v_reusejp_1800_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v_a_1794_);
v___x_1801_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1800_;
}
v_reusejp_1800_:
{
return v___x_1801_;
}
}
}
else
{
lean_dec(v_a_1792_);
return v___x_1793_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___boxed(lean_object* v_input_1805_, lean_object* v_pre_1806_, lean_object* v_post_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_){
_start:
{
lean_object* v_res_1813_; 
v_res_1813_ = l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0(v_input_1805_, v_pre_1806_, v_post_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_);
lean_dec(v___y_1811_);
lean_dec_ref(v___y_1810_);
lean_dec(v___y_1809_);
lean_dec_ref(v___y_1808_);
return v_res_1813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_reduceProjs(lean_object* v_e_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_){
_start:
{
lean_object* v___f_1822_; lean_object* v___f_1823_; lean_object* v___x_1824_; 
v___f_1822_ = ((lean_object*)(l_Lean_Meta_PProdN_reduceProjs___closed__0));
v___f_1823_ = ((lean_object*)(l_Lean_Meta_PProdN_reduceProjs___closed__1));
v___x_1824_ = l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0(v_e_1816_, v___f_1822_, v___f_1823_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_);
return v___x_1824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_reduceProjs___boxed(lean_object* v_e_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_){
_start:
{
lean_object* v_res_1831_; 
v_res_1831_ = l_Lean_Meta_PProdN_reduceProjs(v_e_1825_, v_a_1826_, v_a_1827_, v_a_1828_, v_a_1829_);
lean_dec(v_a_1829_);
lean_dec_ref(v_a_1828_);
lean_dec(v_a_1827_);
lean_dec_ref(v_a_1826_);
return v_res_1831_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_1832_, lean_object* v_m_1833_, lean_object* v_a_1834_){
_start:
{
lean_object* v___x_1835_; 
v___x_1835_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3___redArg(v_m_1833_, v_a_1834_);
return v___x_1835_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_1836_, lean_object* v_m_1837_, lean_object* v_a_1838_){
_start:
{
lean_object* v_res_1839_; 
v_res_1839_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3(v_00_u03b2_1836_, v_m_1837_, v_a_1838_);
lean_dec_ref(v_a_1838_);
lean_dec_ref(v_m_1837_);
return v_res_1839_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_1840_, lean_object* v_ref_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_){
_start:
{
lean_object* v___x_1845_; 
v___x_1845_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_1841_);
return v___x_1845_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1846_, lean_object* v_ref_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_){
_start:
{
lean_object* v_res_1851_; 
v_res_1851_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_1846_, v_ref_1847_, v___y_1848_, v___y_1849_);
lean_dec(v___y_1849_);
lean_dec_ref(v___y_1848_);
return v_res_1851_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__8(lean_object* v_00_u03b1_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_){
_start:
{
lean_object* v___x_1856_; 
v___x_1856_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__8___redArg();
return v___x_1856_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__8___boxed(lean_object* v_00_u03b1_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_){
_start:
{
lean_object* v_res_1861_; 
v_res_1861_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__8(v_00_u03b1_1857_, v___y_1858_, v___y_1859_);
lean_dec(v___y_1859_);
lean_dec_ref(v___y_1858_);
return v_res_1861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5(lean_object* v_00_u03b1_1862_, lean_object* v_x_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_){
_start:
{
lean_object* v___x_1870_; 
v___x_1870_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5___redArg(v_x_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_);
return v___x_1870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b1_1871_, lean_object* v_x_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_){
_start:
{
lean_object* v_res_1879_; 
v_res_1879_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5(v_00_u03b1_1871_, v_x_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_);
lean_dec(v___y_1877_);
lean_dec_ref(v___y_1876_);
lean_dec(v___y_1875_);
lean_dec_ref(v___y_1874_);
lean_dec(v___y_1873_);
return v_res_1879_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6(lean_object* v_00_u03b2_1880_, lean_object* v_m_1881_, lean_object* v_a_1882_, lean_object* v_b_1883_){
_start:
{
lean_object* v___x_1884_; 
v___x_1884_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6___redArg(v_m_1881_, v_a_1882_, v_b_1883_);
return v___x_1884_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b2_1885_, lean_object* v_a_1886_, lean_object* v_x_1887_){
_start:
{
lean_object* v___x_1888_; 
v___x_1888_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3_spec__4___redArg(v_a_1886_, v_x_1887_);
return v___x_1888_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3_spec__4___boxed(lean_object* v_00_u03b2_1889_, lean_object* v_a_1890_, lean_object* v_x_1891_){
_start:
{
lean_object* v_res_1892_; 
v_res_1892_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3_spec__4(v_00_u03b2_1889_, v_a_1890_, v_x_1891_);
lean_dec(v_x_1891_);
lean_dec_ref(v_a_1890_);
return v_res_1892_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__10(lean_object* v_00_u03b2_1893_, lean_object* v_a_1894_, lean_object* v_x_1895_){
_start:
{
uint8_t v___x_1896_; 
v___x_1896_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__10___redArg(v_a_1894_, v_x_1895_);
return v___x_1896_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__10___boxed(lean_object* v_00_u03b2_1897_, lean_object* v_a_1898_, lean_object* v_x_1899_){
_start:
{
uint8_t v_res_1900_; lean_object* v_r_1901_; 
v_res_1900_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__10(v_00_u03b2_1897_, v_a_1898_, v_x_1899_);
lean_dec(v_x_1899_);
lean_dec_ref(v_a_1898_);
v_r_1901_ = lean_box(v_res_1900_);
return v_r_1901_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11(lean_object* v_00_u03b2_1902_, lean_object* v_data_1903_){
_start:
{
lean_object* v___x_1904_; 
v___x_1904_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11___redArg(v_data_1903_);
return v___x_1904_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__12(lean_object* v_00_u03b2_1905_, lean_object* v_a_1906_, lean_object* v_b_1907_, lean_object* v_x_1908_){
_start:
{
lean_object* v___x_1909_; 
v___x_1909_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__12___redArg(v_a_1906_, v_b_1907_, v_x_1908_);
return v___x_1909_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11_spec__12(lean_object* v_00_u03b2_1910_, lean_object* v_i_1911_, lean_object* v_source_1912_, lean_object* v_target_1913_){
_start:
{
lean_object* v___x_1914_; 
v___x_1914_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v_i_1911_, v_source_1912_, v_target_1913_);
return v___x_1914_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13(lean_object* v_00_u03b2_1915_, lean_object* v_x_1916_, lean_object* v_x_1917_){
_start:
{
lean_object* v___x_1918_; 
v___x_1918_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_x_1916_, v_x_1917_);
return v___x_1918_;
}
}
lean_object* runtime_initialize_Lean_Meta_Transform(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_PProdN(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Transform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_PProdN(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Transform(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_PProdN(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Transform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_PProdN(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_PProdN(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_PProdN(builtin);
}
#ifdef __cplusplus
}
#endif
