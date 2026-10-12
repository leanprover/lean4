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
lean_object* l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
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
uint8_t l_Lean_Expr_isProj(lean_object*);
lean_object* l_Lean_Expr_projExpr_x21(lean_object*);
lean_object* l_Lean_Expr_projIdx_x21(lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_Meta_PProdN_genMk___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_PProdN_genMk___redArg___closed__0;
static lean_once_cell_t l_Lean_Meta_PProdN_genMk___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_PProdN_genMk___redArg___closed__1;
static const lean_closure_object l_Lean_Meta_PProdN_genMk___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_PProdN_genMk___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_PProdN_genMk___redArg___closed__2_value;
static const lean_closure_object l_Lean_Meta_PProdN_genMk___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_PProdN_genMk___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_PProdN_genMk___redArg___closed__3_value;
static const lean_closure_object l_Lean_Meta_PProdN_genMk___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_PProdN_genMk___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_PProdN_genMk___redArg___closed__4_value;
static const lean_closure_object l_Lean_Meta_PProdN_genMk___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_PProdN_genMk___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_PProdN_genMk___redArg___closed__5_value;
static const lean_closure_object l_Lean_Meta_PProdN_genMk___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_PProdN_genMk___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_PProdN_genMk___redArg___closed__6_value;
static const lean_string_object l_Lean_Meta_PProdN_genMk___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.Meta.PProdN.genMk"};
static const lean_object* l_Lean_Meta_PProdN_genMk___redArg___closed__7 = (const lean_object*)&l_Lean_Meta_PProdN_genMk___redArg___closed__7_value;
static const lean_string_object l_Lean_Meta_PProdN_genMk___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "assertion violation: !xs.isEmpty\n  "};
static const lean_object* l_Lean_Meta_PProdN_genMk___redArg___closed__8 = (const lean_object*)&l_Lean_Meta_PProdN_genMk___redArg___closed__8_value;
static lean_once_cell_t l_Lean_Meta_PProdN_genMk___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_PProdN_genMk___redArg___closed__9;
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
lean_object* l_Lean_Meta_mkPProd(lean_object* v_e1_10_, lean_object* v_e2_11_, lean_object* v_a_12_, lean_object* v_a_13_, lean_object* v_a_14_, lean_object* v_a_15_){
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
LEAN_EXPORT void l_Lean_Meta_mkPProd_0interp(lean_interpreter_value* stack)
{
lean_object* v_e1_10_ = stack[0].m_obj;
lean_object* v_e2_11_ = stack[1].m_obj;
lean_object* v_a_12_ = stack[2].m_obj;
lean_object* v_a_13_ = stack[3].m_obj;
lean_object* v_a_14_ = stack[4].m_obj;
lean_object* v_a_15_ = stack[5].m_obj;
lean_object* v_res_59_;
v_res_59_ = l_Lean_Meta_mkPProd(v_e1_10_, v_e2_11_, v_a_12_, v_a_13_, v_a_14_, v_a_15_);
stack->m_obj
 = v_res_59_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPProd___boxed(lean_object* v_e1_60_, lean_object* v_e2_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Lean_Meta_mkPProd(v_e1_60_, v_e2_61_, v_a_62_, v_a_63_, v_a_64_, v_a_65_);
lean_dec(v_a_65_);
lean_dec_ref(v_a_64_);
lean_dec(v_a_63_);
lean_dec_ref(v_a_62_);
return v_res_67_;
}
}
static lean_object* _init_l_Lean_Meta_mkPProdMk___closed__4(void){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_76_ = lean_box(0);
v___x_77_ = ((lean_object*)(l_Lean_Meta_mkPProdMk___closed__3));
v___x_78_ = l_Lean_Expr_const___override(v___x_77_, v___x_76_);
return v___x_78_;
}
}
lean_object* l_Lean_Meta_mkPProdMk(lean_object* v_e1_79_, lean_object* v_e2_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_){
_start:
{
lean_object* v___x_86_; 
lean_inc(v_a_84_);
lean_inc_ref(v_a_83_);
lean_inc(v_a_82_);
lean_inc_ref(v_a_81_);
lean_inc_ref(v_e1_79_);
v___x_86_ = lean_infer_type(v_e1_79_, v_a_81_, v_a_82_, v_a_83_, v_a_84_);
if (lean_obj_tag(v___x_86_) == 0)
{
lean_object* v_a_87_; lean_object* v___x_88_; 
v_a_87_ = lean_ctor_get(v___x_86_, 0);
lean_inc(v_a_87_);
lean_dec_ref_known(v___x_86_, 1);
lean_inc(v_a_84_);
lean_inc_ref(v_a_83_);
lean_inc(v_a_82_);
lean_inc_ref(v_a_81_);
lean_inc_ref(v_e2_80_);
v___x_88_ = lean_infer_type(v_e2_80_, v_a_81_, v_a_82_, v_a_83_, v_a_84_);
if (lean_obj_tag(v___x_88_) == 0)
{
lean_object* v_a_89_; lean_object* v___x_90_; 
v_a_89_ = lean_ctor_get(v___x_88_, 0);
lean_inc(v_a_89_);
lean_dec_ref_known(v___x_88_, 1);
lean_inc(v_a_87_);
v___x_90_ = l_Lean_Meta_getLevel(v_a_87_, v_a_81_, v_a_82_, v_a_83_, v_a_84_);
if (lean_obj_tag(v___x_90_) == 0)
{
lean_object* v_a_91_; lean_object* v___x_92_; 
v_a_91_ = lean_ctor_get(v___x_90_, 0);
lean_inc(v_a_91_);
lean_dec_ref_known(v___x_90_, 1);
lean_inc(v_a_89_);
v___x_92_ = l_Lean_Meta_getLevel(v_a_89_, v_a_81_, v_a_82_, v_a_83_, v_a_84_);
if (lean_obj_tag(v___x_92_) == 0)
{
lean_object* v_a_93_; lean_object* v___x_95_; uint8_t v_isShared_96_; uint8_t v_isSharedCheck_115_; 
v_a_93_ = lean_ctor_get(v___x_92_, 0);
v_isSharedCheck_115_ = !lean_is_exclusive(v___x_92_);
if (v_isSharedCheck_115_ == 0)
{
v___x_95_ = v___x_92_;
v_isShared_96_ = v_isSharedCheck_115_;
goto v_resetjp_94_;
}
else
{
lean_inc(v_a_93_);
lean_dec(v___x_92_);
v___x_95_ = lean_box(0);
v_isShared_96_ = v_isSharedCheck_115_;
goto v_resetjp_94_;
}
v_resetjp_94_:
{
uint8_t v___y_98_; uint8_t v___x_113_; 
v___x_113_ = l_Lean_Level_isAlwaysZero(v_a_91_);
if (v___x_113_ == 0)
{
v___y_98_ = v___x_113_;
goto v___jp_97_;
}
else
{
uint8_t v___x_114_; 
v___x_114_ = l_Lean_Level_isAlwaysZero(v_a_93_);
v___y_98_ = v___x_114_;
goto v___jp_97_;
}
v___jp_97_:
{
if (v___y_98_ == 0)
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_106_; 
v___x_99_ = ((lean_object*)(l_Lean_Meta_mkPProdMk___closed__1));
v___x_100_ = lean_box(0);
v___x_101_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_101_, 0, v_a_93_);
lean_ctor_set(v___x_101_, 1, v___x_100_);
v___x_102_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_102_, 0, v_a_91_);
lean_ctor_set(v___x_102_, 1, v___x_101_);
v___x_103_ = l_Lean_Expr_const___override(v___x_99_, v___x_102_);
v___x_104_ = l_Lean_mkApp4(v___x_103_, v_a_87_, v_a_89_, v_e1_79_, v_e2_80_);
if (v_isShared_96_ == 0)
{
lean_ctor_set(v___x_95_, 0, v___x_104_);
v___x_106_ = v___x_95_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v___x_104_);
v___x_106_ = v_reuseFailAlloc_107_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
return v___x_106_;
}
}
else
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_111_; 
lean_dec(v_a_93_);
lean_dec(v_a_91_);
v___x_108_ = lean_obj_once(&l_Lean_Meta_mkPProdMk___closed__4, &l_Lean_Meta_mkPProdMk___closed__4_once, _init_l_Lean_Meta_mkPProdMk___closed__4);
v___x_109_ = l_Lean_mkApp4(v___x_108_, v_a_87_, v_a_89_, v_e1_79_, v_e2_80_);
if (v_isShared_96_ == 0)
{
lean_ctor_set(v___x_95_, 0, v___x_109_);
v___x_111_ = v___x_95_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v___x_109_);
v___x_111_ = v_reuseFailAlloc_112_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
return v___x_111_;
}
}
}
}
}
else
{
lean_object* v_a_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_123_; 
lean_dec(v_a_91_);
lean_dec(v_a_89_);
lean_dec(v_a_87_);
lean_dec_ref(v_e2_80_);
lean_dec_ref(v_e1_79_);
v_a_116_ = lean_ctor_get(v___x_92_, 0);
v_isSharedCheck_123_ = !lean_is_exclusive(v___x_92_);
if (v_isSharedCheck_123_ == 0)
{
v___x_118_ = v___x_92_;
v_isShared_119_ = v_isSharedCheck_123_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_a_116_);
lean_dec(v___x_92_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_123_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
lean_object* v___x_121_; 
if (v_isShared_119_ == 0)
{
v___x_121_ = v___x_118_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v_a_116_);
v___x_121_ = v_reuseFailAlloc_122_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
return v___x_121_;
}
}
}
}
else
{
lean_object* v_a_124_; lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_131_; 
lean_dec(v_a_89_);
lean_dec(v_a_87_);
lean_dec_ref(v_e2_80_);
lean_dec_ref(v_e1_79_);
v_a_124_ = lean_ctor_get(v___x_90_, 0);
v_isSharedCheck_131_ = !lean_is_exclusive(v___x_90_);
if (v_isSharedCheck_131_ == 0)
{
v___x_126_ = v___x_90_;
v_isShared_127_ = v_isSharedCheck_131_;
goto v_resetjp_125_;
}
else
{
lean_inc(v_a_124_);
lean_dec(v___x_90_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_131_;
goto v_resetjp_125_;
}
v_resetjp_125_:
{
lean_object* v___x_129_; 
if (v_isShared_127_ == 0)
{
v___x_129_ = v___x_126_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v_a_124_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
return v___x_129_;
}
}
}
}
else
{
lean_dec(v_a_87_);
lean_dec_ref(v_e2_80_);
lean_dec_ref(v_e1_79_);
return v___x_88_;
}
}
else
{
lean_dec_ref(v_e2_80_);
lean_dec_ref(v_e1_79_);
return v___x_86_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_mkPProdMk_0interp(lean_interpreter_value* stack)
{
lean_object* v_e1_79_ = stack[0].m_obj;
lean_object* v_e2_80_ = stack[1].m_obj;
lean_object* v_a_81_ = stack[2].m_obj;
lean_object* v_a_82_ = stack[3].m_obj;
lean_object* v_a_83_ = stack[4].m_obj;
lean_object* v_a_84_ = stack[5].m_obj;
lean_object* v_res_132_;
v_res_132_ = l_Lean_Meta_mkPProdMk(v_e1_79_, v_e2_80_, v_a_81_, v_a_82_, v_a_83_, v_a_84_);
stack->m_obj
 = v_res_132_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPProdMk___boxed(lean_object* v_e1_133_, lean_object* v_e2_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_Lean_Meta_mkPProdMk(v_e1_133_, v_e2_134_, v_a_135_, v_a_136_, v_a_137_, v_a_138_);
lean_dec(v_a_138_);
lean_dec_ref(v_a_137_);
lean_dec(v_a_136_);
lean_dec_ref(v_a_135_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkPProdFst_spec__0(lean_object* v_msg_141_){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_142_ = l_Lean_instInhabitedExpr;
v___x_143_ = lean_panic_fn_borrowed(v___x_142_, v_msg_141_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPProdFst(lean_object* v_t_148_, lean_object* v_e_149_){
_start:
{
lean_object* v___x_164_; uint8_t v___x_165_; 
lean_inc_ref(v_t_148_);
v___x_164_ = l_Lean_Expr_cleanupAnnotations(v_t_148_);
v___x_165_ = l_Lean_Expr_isApp(v___x_164_);
if (v___x_165_ == 0)
{
lean_dec_ref(v___x_164_);
goto v___jp_150_;
}
else
{
lean_object* v___x_166_; uint8_t v___x_167_; 
v___x_166_ = l_Lean_Expr_appFnCleanup___redArg(v___x_164_);
v___x_167_ = l_Lean_Expr_isApp(v___x_166_);
if (v___x_167_ == 0)
{
lean_dec_ref(v___x_166_);
goto v___jp_150_;
}
else
{
lean_object* v___x_168_; lean_object* v___x_169_; uint8_t v___x_170_; 
v___x_168_ = l_Lean_Expr_appFnCleanup___redArg(v___x_166_);
v___x_169_ = ((lean_object*)(l_Lean_Meta_mkPProd___closed__3));
v___x_170_ = l_Lean_Expr_isConstOf(v___x_168_, v___x_169_);
if (v___x_170_ == 0)
{
lean_object* v___x_171_; uint8_t v___x_172_; 
v___x_171_ = ((lean_object*)(l_Lean_Meta_mkPProd___closed__1));
v___x_172_ = l_Lean_Expr_isConstOf(v___x_168_, v___x_171_);
lean_dec_ref(v___x_168_);
if (v___x_172_ == 0)
{
goto v___jp_150_;
}
else
{
lean_object* v___x_173_; lean_object* v___x_174_; 
lean_dec_ref(v_t_148_);
v___x_173_ = lean_unsigned_to_nat(0u);
v___x_174_ = l_Lean_Expr_proj___override(v___x_171_, v___x_173_, v_e_149_);
return v___x_174_;
}
}
else
{
lean_object* v___x_175_; lean_object* v___x_176_; 
lean_dec_ref(v___x_168_);
lean_dec_ref(v_t_148_);
v___x_175_ = lean_unsigned_to_nat(0u);
v___x_176_ = l_Lean_Expr_proj___override(v___x_169_, v___x_175_, v_e_149_);
return v___x_176_;
}
}
}
v___jp_150_:
{
lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_151_ = ((lean_object*)(l_Lean_Meta_mkPProdFst___closed__0));
v___x_152_ = ((lean_object*)(l_Lean_Meta_mkPProdFst___closed__1));
v___x_153_ = lean_unsigned_to_nat(60u);
v___x_154_ = lean_unsigned_to_nat(9u);
v___x_155_ = ((lean_object*)(l_Lean_Meta_mkPProdFst___closed__2));
v___x_156_ = lean_expr_dbg_to_string(v_e_149_);
lean_dec_ref(v_e_149_);
v___x_157_ = lean_string_append(v___x_155_, v___x_156_);
lean_dec_ref(v___x_156_);
v___x_158_ = ((lean_object*)(l_Lean_Meta_mkPProdFst___closed__3));
v___x_159_ = lean_string_append(v___x_157_, v___x_158_);
v___x_160_ = lean_expr_dbg_to_string(v_t_148_);
lean_dec_ref(v_t_148_);
v___x_161_ = lean_string_append(v___x_159_, v___x_160_);
lean_dec_ref(v___x_160_);
v___x_162_ = l_mkPanicMessageWithDecl(v___x_151_, v___x_152_, v___x_153_, v___x_154_, v___x_161_);
lean_dec_ref(v___x_161_);
v___x_163_ = l_panic___at___00Lean_Meta_mkPProdFst_spec__0(v___x_162_);
return v___x_163_;
}
}
}
lean_object* l_Lean_Meta_mkPProdFstM(lean_object* v_e_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_){
_start:
{
lean_object* v___x_183_; 
lean_inc(v_a_181_);
lean_inc_ref(v_a_180_);
lean_inc(v_a_179_);
lean_inc_ref(v_a_178_);
lean_inc_ref(v_e_177_);
v___x_183_ = lean_infer_type(v_e_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_);
if (lean_obj_tag(v___x_183_) == 0)
{
lean_object* v_a_184_; lean_object* v___x_185_; 
v_a_184_ = lean_ctor_get(v___x_183_, 0);
lean_inc(v_a_184_);
lean_dec_ref_known(v___x_183_, 1);
lean_inc(v_a_181_);
lean_inc_ref(v_a_180_);
lean_inc(v_a_179_);
lean_inc_ref(v_a_178_);
v___x_185_ = lean_whnf(v_a_184_, v_a_178_, v_a_179_, v_a_180_, v_a_181_);
if (lean_obj_tag(v___x_185_) == 0)
{
lean_object* v_a_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_194_; 
v_a_186_ = lean_ctor_get(v___x_185_, 0);
v_isSharedCheck_194_ = !lean_is_exclusive(v___x_185_);
if (v_isSharedCheck_194_ == 0)
{
v___x_188_ = v___x_185_;
v_isShared_189_ = v_isSharedCheck_194_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_a_186_);
lean_dec(v___x_185_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_194_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v___x_190_; lean_object* v___x_192_; 
v___x_190_ = l_Lean_Meta_mkPProdFst(v_a_186_, v_e_177_);
if (v_isShared_189_ == 0)
{
lean_ctor_set(v___x_188_, 0, v___x_190_);
v___x_192_ = v___x_188_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v___x_190_);
v___x_192_ = v_reuseFailAlloc_193_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
return v___x_192_;
}
}
}
else
{
lean_dec_ref(v_e_177_);
return v___x_185_;
}
}
else
{
lean_dec_ref(v_e_177_);
return v___x_183_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_mkPProdFstM_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_177_ = stack[0].m_obj;
lean_object* v_a_178_ = stack[1].m_obj;
lean_object* v_a_179_ = stack[2].m_obj;
lean_object* v_a_180_ = stack[3].m_obj;
lean_object* v_a_181_ = stack[4].m_obj;
lean_object* v_res_195_;
v_res_195_ = l_Lean_Meta_mkPProdFstM(v_e_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_);
stack->m_obj
 = v_res_195_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPProdFstM___boxed(lean_object* v_e_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l_Lean_Meta_mkPProdFstM(v_e_196_, v_a_197_, v_a_198_, v_a_199_, v_a_200_);
lean_dec(v_a_200_);
lean_dec_ref(v_a_199_);
lean_dec(v_a_198_);
lean_dec_ref(v_a_197_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PProdN_0__Lean_Meta_mkTypeSnd(lean_object* v_t_205_){
_start:
{
lean_object* v___x_216_; uint8_t v___x_217_; 
lean_inc_ref(v_t_205_);
v___x_216_ = l_Lean_Expr_cleanupAnnotations(v_t_205_);
v___x_217_ = l_Lean_Expr_isApp(v___x_216_);
if (v___x_217_ == 0)
{
lean_dec_ref(v___x_216_);
goto v___jp_206_;
}
else
{
lean_object* v_arg_218_; lean_object* v___x_219_; uint8_t v___x_220_; 
v_arg_218_ = lean_ctor_get(v___x_216_, 1);
lean_inc_ref(v_arg_218_);
v___x_219_ = l_Lean_Expr_appFnCleanup___redArg(v___x_216_);
v___x_220_ = l_Lean_Expr_isApp(v___x_219_);
if (v___x_220_ == 0)
{
lean_dec_ref(v___x_219_);
lean_dec_ref(v_arg_218_);
goto v___jp_206_;
}
else
{
lean_object* v___x_221_; lean_object* v___x_222_; uint8_t v___x_223_; 
v___x_221_ = l_Lean_Expr_appFnCleanup___redArg(v___x_219_);
v___x_222_ = ((lean_object*)(l_Lean_Meta_mkPProd___closed__3));
v___x_223_ = l_Lean_Expr_isConstOf(v___x_221_, v___x_222_);
if (v___x_223_ == 0)
{
lean_object* v___x_224_; uint8_t v___x_225_; 
v___x_224_ = ((lean_object*)(l_Lean_Meta_mkPProd___closed__1));
v___x_225_ = l_Lean_Expr_isConstOf(v___x_221_, v___x_224_);
lean_dec_ref(v___x_221_);
if (v___x_225_ == 0)
{
lean_dec_ref(v_arg_218_);
goto v___jp_206_;
}
else
{
lean_dec_ref(v_t_205_);
return v_arg_218_;
}
}
else
{
lean_dec_ref(v___x_221_);
lean_dec_ref(v_t_205_);
return v_arg_218_;
}
}
}
v___jp_206_:
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_207_ = ((lean_object*)(l_Lean_Meta_mkPProdFst___closed__0));
v___x_208_ = ((lean_object*)(l___private_Lean_Meta_PProdN_0__Lean_Meta_mkTypeSnd___closed__0));
v___x_209_ = lean_unsigned_to_nat(70u);
v___x_210_ = lean_unsigned_to_nat(9u);
v___x_211_ = ((lean_object*)(l___private_Lean_Meta_PProdN_0__Lean_Meta_mkTypeSnd___closed__1));
v___x_212_ = lean_expr_dbg_to_string(v_t_205_);
lean_dec_ref(v_t_205_);
v___x_213_ = lean_string_append(v___x_211_, v___x_212_);
lean_dec_ref(v___x_212_);
v___x_214_ = l_mkPanicMessageWithDecl(v___x_207_, v___x_208_, v___x_209_, v___x_210_, v___x_213_);
lean_dec_ref(v___x_213_);
v___x_215_ = l_panic___at___00Lean_Meta_mkPProdFst_spec__0(v___x_214_);
return v___x_215_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPProdSnd(lean_object* v_t_228_, lean_object* v_e_229_){
_start:
{
lean_object* v___x_244_; uint8_t v___x_245_; 
lean_inc_ref(v_t_228_);
v___x_244_ = l_Lean_Expr_cleanupAnnotations(v_t_228_);
v___x_245_ = l_Lean_Expr_isApp(v___x_244_);
if (v___x_245_ == 0)
{
lean_dec_ref(v___x_244_);
goto v___jp_230_;
}
else
{
lean_object* v___x_246_; uint8_t v___x_247_; 
v___x_246_ = l_Lean_Expr_appFnCleanup___redArg(v___x_244_);
v___x_247_ = l_Lean_Expr_isApp(v___x_246_);
if (v___x_247_ == 0)
{
lean_dec_ref(v___x_246_);
goto v___jp_230_;
}
else
{
lean_object* v___x_248_; lean_object* v___x_249_; uint8_t v___x_250_; 
v___x_248_ = l_Lean_Expr_appFnCleanup___redArg(v___x_246_);
v___x_249_ = ((lean_object*)(l_Lean_Meta_mkPProd___closed__3));
v___x_250_ = l_Lean_Expr_isConstOf(v___x_248_, v___x_249_);
if (v___x_250_ == 0)
{
lean_object* v___x_251_; uint8_t v___x_252_; 
v___x_251_ = ((lean_object*)(l_Lean_Meta_mkPProd___closed__1));
v___x_252_ = l_Lean_Expr_isConstOf(v___x_248_, v___x_251_);
lean_dec_ref(v___x_248_);
if (v___x_252_ == 0)
{
goto v___jp_230_;
}
else
{
lean_object* v___x_253_; lean_object* v___x_254_; 
lean_dec_ref(v_t_228_);
v___x_253_ = lean_unsigned_to_nat(1u);
v___x_254_ = l_Lean_Expr_proj___override(v___x_251_, v___x_253_, v_e_229_);
return v___x_254_;
}
}
else
{
lean_object* v___x_255_; lean_object* v___x_256_; 
lean_dec_ref(v___x_248_);
lean_dec_ref(v_t_228_);
v___x_255_ = lean_unsigned_to_nat(1u);
v___x_256_ = l_Lean_Expr_proj___override(v___x_249_, v___x_255_, v_e_229_);
return v___x_256_;
}
}
}
v___jp_230_:
{
lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_231_ = ((lean_object*)(l_Lean_Meta_mkPProdFst___closed__0));
v___x_232_ = ((lean_object*)(l_Lean_Meta_mkPProdSnd___closed__0));
v___x_233_ = lean_unsigned_to_nat(77u);
v___x_234_ = lean_unsigned_to_nat(9u);
v___x_235_ = ((lean_object*)(l_Lean_Meta_mkPProdSnd___closed__1));
v___x_236_ = lean_expr_dbg_to_string(v_e_229_);
lean_dec_ref(v_e_229_);
v___x_237_ = lean_string_append(v___x_235_, v___x_236_);
lean_dec_ref(v___x_236_);
v___x_238_ = ((lean_object*)(l_Lean_Meta_mkPProdFst___closed__3));
v___x_239_ = lean_string_append(v___x_237_, v___x_238_);
v___x_240_ = lean_expr_dbg_to_string(v_t_228_);
lean_dec_ref(v_t_228_);
v___x_241_ = lean_string_append(v___x_239_, v___x_240_);
lean_dec_ref(v___x_240_);
v___x_242_ = l_mkPanicMessageWithDecl(v___x_231_, v___x_232_, v___x_233_, v___x_234_, v___x_241_);
lean_dec_ref(v___x_241_);
v___x_243_ = l_panic___at___00Lean_Meta_mkPProdFst_spec__0(v___x_242_);
return v___x_243_;
}
}
}
lean_object* l_Lean_Meta_mkPProdSndM(lean_object* v_e_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_){
_start:
{
lean_object* v___x_263_; 
lean_inc(v_a_261_);
lean_inc_ref(v_a_260_);
lean_inc(v_a_259_);
lean_inc_ref(v_a_258_);
lean_inc_ref(v_e_257_);
v___x_263_ = lean_infer_type(v_e_257_, v_a_258_, v_a_259_, v_a_260_, v_a_261_);
if (lean_obj_tag(v___x_263_) == 0)
{
lean_object* v_a_264_; lean_object* v___x_265_; 
v_a_264_ = lean_ctor_get(v___x_263_, 0);
lean_inc(v_a_264_);
lean_dec_ref_known(v___x_263_, 1);
lean_inc(v_a_261_);
lean_inc_ref(v_a_260_);
lean_inc(v_a_259_);
lean_inc_ref(v_a_258_);
v___x_265_ = lean_whnf(v_a_264_, v_a_258_, v_a_259_, v_a_260_, v_a_261_);
if (lean_obj_tag(v___x_265_) == 0)
{
lean_object* v_a_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_274_; 
v_a_266_ = lean_ctor_get(v___x_265_, 0);
v_isSharedCheck_274_ = !lean_is_exclusive(v___x_265_);
if (v_isSharedCheck_274_ == 0)
{
v___x_268_ = v___x_265_;
v_isShared_269_ = v_isSharedCheck_274_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_a_266_);
lean_dec(v___x_265_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_274_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v___x_270_; lean_object* v___x_272_; 
v___x_270_ = l_Lean_Meta_mkPProdSnd(v_a_266_, v_e_257_);
if (v_isShared_269_ == 0)
{
lean_ctor_set(v___x_268_, 0, v___x_270_);
v___x_272_ = v___x_268_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v___x_270_);
v___x_272_ = v_reuseFailAlloc_273_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
return v___x_272_;
}
}
}
else
{
lean_dec_ref(v_e_257_);
return v___x_265_;
}
}
else
{
lean_dec_ref(v_e_257_);
return v___x_263_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_mkPProdSndM_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_257_ = stack[0].m_obj;
lean_object* v_a_258_ = stack[1].m_obj;
lean_object* v_a_259_ = stack[2].m_obj;
lean_object* v_a_260_ = stack[3].m_obj;
lean_object* v_a_261_ = stack[4].m_obj;
lean_object* v_res_275_;
v_res_275_ = l_Lean_Meta_mkPProdSndM(v_e_257_, v_a_258_, v_a_259_, v_a_260_, v_a_261_);
stack->m_obj
 = v_res_275_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPProdSndM___boxed(lean_object* v_e_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l_Lean_Meta_mkPProdSndM(v_e_276_, v_a_277_, v_a_278_, v_a_279_, v_a_280_);
lean_dec(v_a_280_);
lean_dec_ref(v_a_279_);
lean_dec(v_a_278_);
lean_dec_ref(v_a_277_);
return v_res_282_;
}
}
static lean_object* _init_l_Lean_Meta_PProdN_genMk___redArg___closed__0(void){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = l_instMonadEIO___redArg();
return v___x_283_;
}
}
static lean_object* _init_l_Lean_Meta_PProdN_genMk___redArg___closed__1(void){
_start:
{
lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_284_ = lean_obj_once(&l_Lean_Meta_PProdN_genMk___redArg___closed__0, &l_Lean_Meta_PProdN_genMk___redArg___closed__0_once, _init_l_Lean_Meta_PProdN_genMk___redArg___closed__0);
v___x_285_ = l_StateRefT_x27_instMonad___redArg(v___x_284_);
return v___x_285_;
}
}
static lean_object* _init_l_Lean_Meta_PProdN_genMk___redArg___closed__9(void){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_293_ = ((lean_object*)(l_Lean_Meta_PProdN_genMk___redArg___closed__8));
v___x_294_ = lean_unsigned_to_nat(2u);
v___x_295_ = lean_unsigned_to_nat(90u);
v___x_296_ = ((lean_object*)(l_Lean_Meta_PProdN_genMk___redArg___closed__7));
v___x_297_ = ((lean_object*)(l_Lean_Meta_mkPProdFst___closed__0));
v___x_298_ = l_mkPanicMessageWithDecl(v___x_297_, v___x_296_, v___x_295_, v___x_294_, v___x_293_);
return v___x_298_;
}
}
lean_object* l_Lean_Meta_PProdN_genMk___redArg(lean_object* v_inst_299_, lean_object* v_mk_300_, lean_object* v_xs_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_){
_start:
{
lean_object* v___x_307_; lean_object* v_toApplicative_308_; lean_object* v_toFunctor_309_; lean_object* v_toSeq_310_; lean_object* v_toSeqLeft_311_; lean_object* v_toSeqRight_312_; lean_object* v___f_313_; lean_object* v___f_314_; lean_object* v___f_315_; lean_object* v___f_316_; lean_object* v___x_317_; lean_object* v___f_318_; lean_object* v___f_319_; lean_object* v___f_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v_toApplicative_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_369_; 
v___x_307_ = lean_obj_once(&l_Lean_Meta_PProdN_genMk___redArg___closed__1, &l_Lean_Meta_PProdN_genMk___redArg___closed__1_once, _init_l_Lean_Meta_PProdN_genMk___redArg___closed__1);
v_toApplicative_308_ = lean_ctor_get(v___x_307_, 0);
v_toFunctor_309_ = lean_ctor_get(v_toApplicative_308_, 0);
v_toSeq_310_ = lean_ctor_get(v_toApplicative_308_, 2);
v_toSeqLeft_311_ = lean_ctor_get(v_toApplicative_308_, 3);
v_toSeqRight_312_ = lean_ctor_get(v_toApplicative_308_, 4);
v___f_313_ = ((lean_object*)(l_Lean_Meta_PProdN_genMk___redArg___closed__2));
v___f_314_ = ((lean_object*)(l_Lean_Meta_PProdN_genMk___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_309_, 2);
v___f_315_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_315_, 0, v_toFunctor_309_);
v___f_316_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_316_, 0, v_toFunctor_309_);
v___x_317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_317_, 0, v___f_315_);
lean_ctor_set(v___x_317_, 1, v___f_316_);
lean_inc(v_toSeqRight_312_);
v___f_318_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_318_, 0, v_toSeqRight_312_);
lean_inc(v_toSeqLeft_311_);
v___f_319_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_319_, 0, v_toSeqLeft_311_);
lean_inc(v_toSeq_310_);
v___f_320_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_320_, 0, v_toSeq_310_);
v___x_321_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_321_, 0, v___x_317_);
lean_ctor_set(v___x_321_, 1, v___f_313_);
lean_ctor_set(v___x_321_, 2, v___f_320_);
lean_ctor_set(v___x_321_, 3, v___f_319_);
lean_ctor_set(v___x_321_, 4, v___f_318_);
v___x_322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
lean_ctor_set(v___x_322_, 1, v___f_314_);
v___x_323_ = l_StateRefT_x27_instMonad___redArg(v___x_322_);
v_toApplicative_324_ = lean_ctor_get(v___x_323_, 0);
v_isSharedCheck_369_ = !lean_is_exclusive(v___x_323_);
if (v_isSharedCheck_369_ == 0)
{
lean_object* v_unused_370_; 
v_unused_370_ = lean_ctor_get(v___x_323_, 1);
lean_dec(v_unused_370_);
v___x_326_ = v___x_323_;
v_isShared_327_ = v_isSharedCheck_369_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_toApplicative_324_);
lean_dec(v___x_323_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_369_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v_toFunctor_328_; lean_object* v_toSeq_329_; lean_object* v_toSeqLeft_330_; lean_object* v_toSeqRight_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_367_; 
v_toFunctor_328_ = lean_ctor_get(v_toApplicative_324_, 0);
v_toSeq_329_ = lean_ctor_get(v_toApplicative_324_, 2);
v_toSeqLeft_330_ = lean_ctor_get(v_toApplicative_324_, 3);
v_toSeqRight_331_ = lean_ctor_get(v_toApplicative_324_, 4);
v_isSharedCheck_367_ = !lean_is_exclusive(v_toApplicative_324_);
if (v_isSharedCheck_367_ == 0)
{
lean_object* v_unused_368_; 
v_unused_368_ = lean_ctor_get(v_toApplicative_324_, 1);
lean_dec(v_unused_368_);
v___x_333_ = v_toApplicative_324_;
v_isShared_334_ = v_isSharedCheck_367_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_toSeqRight_331_);
lean_inc(v_toSeqLeft_330_);
lean_inc(v_toSeq_329_);
lean_inc(v_toFunctor_328_);
lean_dec(v_toApplicative_324_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_367_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___f_335_; lean_object* v___f_336_; lean_object* v___f_337_; lean_object* v___f_338_; lean_object* v___x_339_; lean_object* v___f_340_; lean_object* v___f_341_; lean_object* v___f_342_; lean_object* v___x_344_; 
v___f_335_ = ((lean_object*)(l_Lean_Meta_PProdN_genMk___redArg___closed__4));
v___f_336_ = ((lean_object*)(l_Lean_Meta_PProdN_genMk___redArg___closed__5));
lean_inc_ref(v_toFunctor_328_);
v___f_337_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_337_, 0, v_toFunctor_328_);
v___f_338_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_338_, 0, v_toFunctor_328_);
v___x_339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_339_, 0, v___f_337_);
lean_ctor_set(v___x_339_, 1, v___f_338_);
v___f_340_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_340_, 0, v_toSeqRight_331_);
v___f_341_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_341_, 0, v_toSeqLeft_330_);
v___f_342_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_342_, 0, v_toSeq_329_);
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 4, v___f_340_);
lean_ctor_set(v___x_333_, 3, v___f_341_);
lean_ctor_set(v___x_333_, 2, v___f_342_);
lean_ctor_set(v___x_333_, 1, v___f_335_);
lean_ctor_set(v___x_333_, 0, v___x_339_);
v___x_344_ = v___x_333_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v___x_339_);
lean_ctor_set(v_reuseFailAlloc_366_, 1, v___f_335_);
lean_ctor_set(v_reuseFailAlloc_366_, 2, v___f_342_);
lean_ctor_set(v_reuseFailAlloc_366_, 3, v___f_341_);
lean_ctor_set(v_reuseFailAlloc_366_, 4, v___f_340_);
v___x_344_ = v_reuseFailAlloc_366_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
lean_object* v___x_346_; 
if (v_isShared_327_ == 0)
{
lean_ctor_set(v___x_326_, 1, v___f_336_);
lean_ctor_set(v___x_326_, 0, v___x_344_);
v___x_346_ = v___x_326_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v___x_344_);
lean_ctor_set(v_reuseFailAlloc_365_, 1, v___f_336_);
v___x_346_ = v_reuseFailAlloc_365_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
lean_object* v___x_347_; lean_object* v___x_348_; uint8_t v___x_349_; 
v___x_347_ = lean_array_get_size(v_xs_301_);
v___x_348_ = lean_unsigned_to_nat(0u);
v___x_349_ = lean_nat_dec_eq(v___x_347_, v___x_348_);
if (v___x_349_ == 0)
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; uint8_t v___x_355_; 
v___x_350_ = lean_unsigned_to_nat(1u);
v___x_351_ = lean_nat_sub(v___x_347_, v___x_350_);
v___x_352_ = lean_array_get(v_inst_299_, v_xs_301_, v___x_351_);
lean_dec(v___x_351_);
v___x_353_ = lean_array_pop(v_xs_301_);
v___x_354_ = lean_array_get_size(v___x_353_);
v___x_355_ = lean_nat_dec_lt(v___x_348_, v___x_354_);
if (v___x_355_ == 0)
{
lean_object* v___x_356_; 
lean_dec_ref(v___x_353_);
lean_dec_ref(v___x_346_);
lean_dec_ref(v_mk_300_);
v___x_356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_356_, 0, v___x_352_);
return v___x_356_;
}
else
{
size_t v___x_357_; size_t v___x_358_; lean_object* v___x_271__overap_359_; lean_object* v___x_360_; 
v___x_357_ = lean_usize_of_nat(v___x_354_);
v___x_358_ = ((size_t)0ULL);
v___x_271__overap_359_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_346_, v_mk_300_, v___x_353_, v___x_357_, v___x_358_, v___x_352_);
lean_inc(v_a_305_);
lean_inc_ref(v_a_304_);
lean_inc(v_a_303_);
lean_inc_ref(v_a_302_);
v___x_360_ = lean_apply_5(v___x_271__overap_359_, v_a_302_, v_a_303_, v_a_304_, v_a_305_, lean_box(0));
return v___x_360_;
}
}
else
{
lean_object* v___f_361_; lean_object* v___x_362_; lean_object* v___x_316__overap_363_; lean_object* v___x_364_; 
lean_dec_ref(v___x_346_);
lean_dec_ref(v_xs_301_);
lean_dec_ref(v_mk_300_);
v___f_361_ = ((lean_object*)(l_Lean_Meta_PProdN_genMk___redArg___closed__6));
v___x_362_ = lean_obj_once(&l_Lean_Meta_PProdN_genMk___redArg___closed__9, &l_Lean_Meta_PProdN_genMk___redArg___closed__9_once, _init_l_Lean_Meta_PProdN_genMk___redArg___closed__9);
v___x_316__overap_363_ = l_panic___redArg(v___f_361_, v___x_362_);
lean_inc(v_a_305_);
lean_inc_ref(v_a_304_);
lean_inc(v_a_303_);
lean_inc_ref(v_a_302_);
v___x_364_ = lean_apply_5(v___x_316__overap_363_, v_a_302_, v_a_303_, v_a_304_, v_a_305_, lean_box(0));
return v___x_364_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_PProdN_genMk___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_299_ = stack[0].m_obj;
lean_object* v_mk_300_ = stack[1].m_obj;
lean_object* v_xs_301_ = stack[2].m_obj;
lean_object* v_a_302_ = stack[3].m_obj;
lean_object* v_a_303_ = stack[4].m_obj;
lean_object* v_a_304_ = stack[5].m_obj;
lean_object* v_a_305_ = stack[6].m_obj;
lean_object* v_res_371_;
v_res_371_ = l_Lean_Meta_PProdN_genMk___redArg(v_inst_299_, v_mk_300_, v_xs_301_, v_a_302_, v_a_303_, v_a_304_, v_a_305_);
stack->m_obj
 = v_res_371_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_genMk___redArg___boxed(lean_object* v_inst_372_, lean_object* v_mk_373_, lean_object* v_xs_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l_Lean_Meta_PProdN_genMk___redArg(v_inst_372_, v_mk_373_, v_xs_374_, v_a_375_, v_a_376_, v_a_377_, v_a_378_);
lean_dec(v_a_378_);
lean_dec_ref(v_a_377_);
lean_dec(v_a_376_);
lean_dec_ref(v_a_375_);
lean_dec(v_inst_372_);
return v_res_380_;
}
}
lean_object* l_Lean_Meta_PProdN_genMk(lean_object* v_00_u03b1_381_, lean_object* v_inst_382_, lean_object* v_mk_383_, lean_object* v_xs_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_){
_start:
{
lean_object* v___x_390_; 
v___x_390_ = l_Lean_Meta_PProdN_genMk___redArg(v_inst_382_, v_mk_383_, v_xs_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_);
return v___x_390_;
}
}
LEAN_EXPORT void l_Lean_Meta_PProdN_genMk_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_382_ = stack[1].m_obj;
lean_object* v_mk_383_ = stack[2].m_obj;
lean_object* v_xs_384_ = stack[3].m_obj;
lean_object* v_a_385_ = stack[4].m_obj;
lean_object* v_a_386_ = stack[5].m_obj;
lean_object* v_a_387_ = stack[6].m_obj;
lean_object* v_a_388_ = stack[7].m_obj;
lean_object* v_res_391_;
v_res_391_ = l_Lean_Meta_PProdN_genMk(lean_box(0), v_inst_382_, v_mk_383_, v_xs_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_);
stack->m_obj
 = v_res_391_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_genMk___boxed(lean_object* v_00_u03b1_392_, lean_object* v_inst_393_, lean_object* v_mk_394_, lean_object* v_xs_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_Lean_Meta_PProdN_genMk(v_00_u03b1_392_, v_inst_393_, v_mk_394_, v_xs_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_);
lean_dec(v_a_399_);
lean_dec_ref(v_a_398_);
lean_dec(v_a_397_);
lean_dec_ref(v_a_396_);
lean_dec(v_inst_393_);
return v_res_401_;
}
}
static lean_object* _init_l_Lean_Meta_PProdN_pack___closed__5(void){
_start:
{
lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_409_ = lean_box(0);
v___x_410_ = ((lean_object*)(l_Lean_Meta_PProdN_pack___closed__4));
v___x_411_ = l_Lean_Expr_const___override(v___x_410_, v___x_409_);
return v___x_411_;
}
}
lean_object* l_Lean_Meta_PProdN_pack(lean_object* v_lvl_412_, lean_object* v_xs_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; uint8_t v___x_421_; 
v___x_419_ = lean_array_get_size(v_xs_413_);
v___x_420_ = lean_unsigned_to_nat(0u);
v___x_421_ = lean_nat_dec_eq(v___x_419_, v___x_420_);
if (v___x_421_ == 0)
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
lean_dec(v_lvl_412_);
v___x_422_ = l_Lean_instInhabitedExpr;
v___x_423_ = ((lean_object*)(l_Lean_Meta_PProdN_pack___closed__0));
v___x_424_ = l_Lean_Meta_PProdN_genMk___redArg(v___x_422_, v___x_423_, v_xs_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_);
return v___x_424_;
}
else
{
uint8_t v___x_425_; 
lean_dec_ref(v_xs_413_);
v___x_425_ = l_Lean_Level_isAlwaysZero(v_lvl_412_);
if (v___x_425_ == 0)
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_426_ = ((lean_object*)(l_Lean_Meta_PProdN_pack___closed__2));
v___x_427_ = lean_box(0);
v___x_428_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_428_, 0, v_lvl_412_);
lean_ctor_set(v___x_428_, 1, v___x_427_);
v___x_429_ = l_Lean_Expr_const___override(v___x_426_, v___x_428_);
v___x_430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_430_, 0, v___x_429_);
return v___x_430_;
}
else
{
lean_object* v___x_431_; lean_object* v___x_432_; 
lean_dec(v_lvl_412_);
v___x_431_ = lean_obj_once(&l_Lean_Meta_PProdN_pack___closed__5, &l_Lean_Meta_PProdN_pack___closed__5_once, _init_l_Lean_Meta_PProdN_pack___closed__5);
v___x_432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_432_, 0, v___x_431_);
return v___x_432_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_PProdN_pack_0interp(lean_interpreter_value* stack)
{
lean_object* v_lvl_412_ = stack[0].m_obj;
lean_object* v_xs_413_ = stack[1].m_obj;
lean_object* v_a_414_ = stack[2].m_obj;
lean_object* v_a_415_ = stack[3].m_obj;
lean_object* v_a_416_ = stack[4].m_obj;
lean_object* v_a_417_ = stack[5].m_obj;
lean_object* v_res_433_;
v_res_433_ = l_Lean_Meta_PProdN_pack(v_lvl_412_, v_xs_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_);
stack->m_obj
 = v_res_433_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_pack___boxed(lean_object* v_lvl_434_, lean_object* v_xs_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_Lean_Meta_PProdN_pack(v_lvl_434_, v_xs_435_, v_a_436_, v_a_437_, v_a_438_, v_a_439_);
lean_dec(v_a_439_);
lean_dec_ref(v_a_438_);
lean_dec(v_a_437_);
lean_dec_ref(v_a_436_);
return v_res_441_;
}
}
lean_object* l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_unpack_go___redArg(lean_object* v_e_442_, lean_object* v_remaining_443_, lean_object* v_acc_444_){
_start:
{
lean_object* v___x_449_; uint8_t v___x_450_; 
v___x_449_ = lean_unsigned_to_nat(0u);
v___x_450_ = lean_nat_dec_eq(v_remaining_443_, v___x_449_);
if (v___x_450_ == 0)
{
if (lean_obj_tag(v_e_442_) == 5)
{
lean_object* v_fn_451_; 
v_fn_451_ = lean_ctor_get(v_e_442_, 0);
if (lean_obj_tag(v_fn_451_) == 5)
{
lean_object* v_fn_452_; 
v_fn_452_ = lean_ctor_get(v_fn_451_, 0);
if (lean_obj_tag(v_fn_452_) == 4)
{
lean_object* v_declName_453_; 
v_declName_453_ = lean_ctor_get(v_fn_452_, 0);
if (lean_obj_tag(v_declName_453_) == 1)
{
lean_object* v_pre_454_; 
v_pre_454_ = lean_ctor_get(v_declName_453_, 0);
if (lean_obj_tag(v_pre_454_) == 0)
{
lean_object* v_arg_455_; lean_object* v_arg_456_; lean_object* v_str_457_; lean_object* v___x_458_; uint8_t v___x_459_; 
v_arg_455_ = lean_ctor_get(v_e_442_, 1);
v_arg_456_ = lean_ctor_get(v_fn_451_, 1);
v_str_457_ = lean_ctor_get(v_declName_453_, 1);
v___x_458_ = ((lean_object*)(l_Lean_Meta_mkPProd___closed__0));
v___x_459_ = lean_string_dec_eq(v_str_457_, v___x_458_);
if (v___x_459_ == 0)
{
lean_dec(v_remaining_443_);
goto v___jp_446_;
}
else
{
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
lean_inc_ref(v_arg_456_);
lean_inc_ref(v_arg_455_);
lean_dec_ref_known(v_e_442_, 2);
v___x_460_ = lean_unsigned_to_nat(1u);
v___x_461_ = lean_nat_sub(v_remaining_443_, v___x_460_);
lean_dec(v_remaining_443_);
v___x_462_ = lean_array_push(v_acc_444_, v_arg_456_);
v_e_442_ = v_arg_455_;
v_remaining_443_ = v___x_461_;
v_acc_444_ = v___x_462_;
goto _start;
}
}
else
{
lean_dec(v_remaining_443_);
goto v___jp_446_;
}
}
else
{
lean_dec(v_remaining_443_);
goto v___jp_446_;
}
}
else
{
lean_dec(v_remaining_443_);
goto v___jp_446_;
}
}
else
{
lean_dec(v_remaining_443_);
goto v___jp_446_;
}
}
else
{
lean_dec(v_remaining_443_);
goto v___jp_446_;
}
}
else
{
lean_object* v___x_464_; 
lean_dec(v_remaining_443_);
lean_dec_ref(v_e_442_);
v___x_464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_464_, 0, v_acc_444_);
return v___x_464_;
}
v___jp_446_:
{
lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_447_ = lean_array_push(v_acc_444_, v_e_442_);
v___x_448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_448_, 0, v___x_447_);
return v___x_448_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_unpack_go___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_442_ = stack[0].m_obj;
lean_object* v_remaining_443_ = stack[1].m_obj;
lean_object* v_acc_444_ = stack[2].m_obj;
lean_object* v_res_465_;
v_res_465_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_unpack_go___redArg(v_e_442_, v_remaining_443_, v_acc_444_);
stack->m_obj
 = v_res_465_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_unpack_go___redArg___boxed(lean_object* v_e_466_, lean_object* v_remaining_467_, lean_object* v_acc_468_, lean_object* v_a_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_unpack_go___redArg(v_e_466_, v_remaining_467_, v_acc_468_);
return v_res_470_;
}
}
lean_object* l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_unpack_go(lean_object* v_e_471_, lean_object* v_remaining_472_, lean_object* v_acc_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_){
_start:
{
lean_object* v___x_479_; 
v___x_479_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_unpack_go___redArg(v_e_471_, v_remaining_472_, v_acc_473_);
return v___x_479_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_unpack_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_471_ = stack[0].m_obj;
lean_object* v_remaining_472_ = stack[1].m_obj;
lean_object* v_acc_473_ = stack[2].m_obj;
lean_object* v_a_474_ = stack[3].m_obj;
lean_object* v_a_475_ = stack[4].m_obj;
lean_object* v_a_476_ = stack[5].m_obj;
lean_object* v_a_477_ = stack[6].m_obj;
lean_object* v_res_480_;
v_res_480_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_unpack_go(v_e_471_, v_remaining_472_, v_acc_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_);
stack->m_obj
 = v_res_480_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_unpack_go___boxed(lean_object* v_e_481_, lean_object* v_remaining_482_, lean_object* v_acc_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_){
_start:
{
lean_object* v_res_489_; 
v_res_489_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_unpack_go(v_e_481_, v_remaining_482_, v_acc_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_);
lean_dec(v_a_487_);
lean_dec_ref(v_a_486_);
lean_dec(v_a_485_);
lean_dec_ref(v_a_484_);
return v_res_489_;
}
}
lean_object* l_Lean_Meta_PProdN_unpack___redArg(lean_object* v_e_492_, lean_object* v_n_493_){
_start:
{
if (lean_obj_tag(v_e_492_) == 4)
{
lean_object* v_declName_501_; 
v_declName_501_ = lean_ctor_get(v_e_492_, 0);
if (lean_obj_tag(v_declName_501_) == 1)
{
lean_object* v_pre_502_; 
v_pre_502_ = lean_ctor_get(v_declName_501_, 0);
if (lean_obj_tag(v_pre_502_) == 0)
{
lean_object* v_str_503_; lean_object* v___x_504_; uint8_t v___x_505_; 
v_str_503_ = lean_ctor_get(v_declName_501_, 1);
v___x_504_ = ((lean_object*)(l_Lean_Meta_PProdN_pack___closed__3));
v___x_505_ = lean_string_dec_eq(v_str_503_, v___x_504_);
if (v___x_505_ == 0)
{
lean_object* v___x_506_; uint8_t v___x_507_; 
v___x_506_ = ((lean_object*)(l_Lean_Meta_PProdN_pack___closed__1));
v___x_507_ = lean_string_dec_eq(v_str_503_, v___x_506_);
if (v___x_507_ == 0)
{
goto v___jp_495_;
}
else
{
lean_dec_ref_known(v_e_492_, 2);
lean_dec(v_n_493_);
goto v___jp_498_;
}
}
else
{
lean_dec_ref_known(v_e_492_, 2);
lean_dec(v_n_493_);
goto v___jp_498_;
}
}
else
{
goto v___jp_495_;
}
}
else
{
goto v___jp_495_;
}
}
else
{
goto v___jp_495_;
}
v___jp_495_:
{
lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_496_ = ((lean_object*)(l_Lean_Meta_PProdN_unpack___redArg___closed__0));
v___x_497_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_unpack_go___redArg(v_e_492_, v_n_493_, v___x_496_);
return v___x_497_;
}
v___jp_498_:
{
lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_499_ = ((lean_object*)(l_Lean_Meta_PProdN_unpack___redArg___closed__0));
v___x_500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_500_, 0, v___x_499_);
return v___x_500_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_PProdN_unpack___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_492_ = stack[0].m_obj;
lean_object* v_n_493_ = stack[1].m_obj;
lean_object* v_res_508_;
v_res_508_ = l_Lean_Meta_PProdN_unpack___redArg(v_e_492_, v_n_493_);
stack->m_obj
 = v_res_508_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_unpack___redArg___boxed(lean_object* v_e_509_, lean_object* v_n_510_, lean_object* v_a_511_){
_start:
{
lean_object* v_res_512_; 
v_res_512_ = l_Lean_Meta_PProdN_unpack___redArg(v_e_509_, v_n_510_);
return v_res_512_;
}
}
lean_object* l_Lean_Meta_PProdN_unpack(lean_object* v_e_513_, lean_object* v_n_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_){
_start:
{
lean_object* v___x_520_; 
v___x_520_ = l_Lean_Meta_PProdN_unpack___redArg(v_e_513_, v_n_514_);
return v___x_520_;
}
}
LEAN_EXPORT void l_Lean_Meta_PProdN_unpack_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_513_ = stack[0].m_obj;
lean_object* v_n_514_ = stack[1].m_obj;
lean_object* v_a_515_ = stack[2].m_obj;
lean_object* v_a_516_ = stack[3].m_obj;
lean_object* v_a_517_ = stack[4].m_obj;
lean_object* v_a_518_ = stack[5].m_obj;
lean_object* v_res_521_;
v_res_521_ = l_Lean_Meta_PProdN_unpack(v_e_513_, v_n_514_, v_a_515_, v_a_516_, v_a_517_, v_a_518_);
stack->m_obj
 = v_res_521_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_unpack___boxed(lean_object* v_e_522_, lean_object* v_n_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l_Lean_Meta_PProdN_unpack(v_e_522_, v_n_523_, v_a_524_, v_a_525_, v_a_526_, v_a_527_);
lean_dec(v_a_527_);
lean_dec_ref(v_a_526_);
lean_dec(v_a_525_);
lean_dec_ref(v_a_524_);
return v_res_529_;
}
}
static lean_object* _init_l_Lean_Meta_PProdN_mk___closed__4(void){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_538_ = lean_box(0);
v___x_539_ = ((lean_object*)(l_Lean_Meta_PProdN_mk___closed__3));
v___x_540_ = l_Lean_Expr_const___override(v___x_539_, v___x_538_);
return v___x_540_;
}
}
lean_object* l_Lean_Meta_PProdN_mk(lean_object* v_lvl_541_, lean_object* v_xs_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_){
_start:
{
lean_object* v___x_548_; lean_object* v___x_549_; uint8_t v___x_550_; 
v___x_548_ = lean_array_get_size(v_xs_542_);
v___x_549_ = lean_unsigned_to_nat(0u);
v___x_550_ = lean_nat_dec_eq(v___x_548_, v___x_549_);
if (v___x_550_ == 0)
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
lean_dec(v_lvl_541_);
v___x_551_ = l_Lean_instInhabitedExpr;
v___x_552_ = ((lean_object*)(l_Lean_Meta_PProdN_mk___closed__0));
v___x_553_ = l_Lean_Meta_PProdN_genMk___redArg(v___x_551_, v___x_552_, v_xs_542_, v_a_543_, v_a_544_, v_a_545_, v_a_546_);
return v___x_553_;
}
else
{
uint8_t v___x_554_; 
lean_dec_ref(v_xs_542_);
v___x_554_ = l_Lean_Level_isAlwaysZero(v_lvl_541_);
if (v___x_554_ == 0)
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_555_ = ((lean_object*)(l_Lean_Meta_PProdN_mk___closed__2));
v___x_556_ = lean_box(0);
v___x_557_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_557_, 0, v_lvl_541_);
lean_ctor_set(v___x_557_, 1, v___x_556_);
v___x_558_ = l_Lean_Expr_const___override(v___x_555_, v___x_557_);
v___x_559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_559_, 0, v___x_558_);
return v___x_559_;
}
else
{
lean_object* v___x_560_; lean_object* v___x_561_; 
lean_dec(v_lvl_541_);
v___x_560_ = lean_obj_once(&l_Lean_Meta_PProdN_mk___closed__4, &l_Lean_Meta_PProdN_mk___closed__4_once, _init_l_Lean_Meta_PProdN_mk___closed__4);
v___x_561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_561_, 0, v___x_560_);
return v___x_561_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_PProdN_mk_0interp(lean_interpreter_value* stack)
{
lean_object* v_lvl_541_ = stack[0].m_obj;
lean_object* v_xs_542_ = stack[1].m_obj;
lean_object* v_a_543_ = stack[2].m_obj;
lean_object* v_a_544_ = stack[3].m_obj;
lean_object* v_a_545_ = stack[4].m_obj;
lean_object* v_a_546_ = stack[5].m_obj;
lean_object* v_res_562_;
v_res_562_ = l_Lean_Meta_PProdN_mk(v_lvl_541_, v_xs_542_, v_a_543_, v_a_544_, v_a_545_, v_a_546_);
stack->m_obj
 = v_res_562_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_mk___boxed(lean_object* v_lvl_563_, lean_object* v_xs_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Lean_Meta_PProdN_mk(v_lvl_563_, v_xs_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_);
lean_dec(v_a_568_);
lean_dec_ref(v_a_567_);
lean_dec(v_a_566_);
lean_dec_ref(v_a_565_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_proj_spec__0___redArg(lean_object* v_upperBound_571_, lean_object* v_a_572_, lean_object* v_b_573_){
_start:
{
uint8_t v___x_574_; 
v___x_574_ = lean_nat_dec_lt(v_a_572_, v_upperBound_571_);
if (v___x_574_ == 0)
{
lean_dec(v_a_572_);
return v_b_573_;
}
else
{
lean_object* v_fst_575_; lean_object* v_snd_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_588_; 
v_fst_575_ = lean_ctor_get(v_b_573_, 0);
v_snd_576_ = lean_ctor_get(v_b_573_, 1);
v_isSharedCheck_588_ = !lean_is_exclusive(v_b_573_);
if (v_isSharedCheck_588_ == 0)
{
v___x_578_ = v_b_573_;
v_isShared_579_ = v_isSharedCheck_588_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_snd_576_);
lean_inc(v_fst_575_);
lean_dec(v_b_573_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_588_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_583_; 
lean_inc(v_fst_575_);
v___x_580_ = l_Lean_Meta_mkPProdSnd(v_fst_575_, v_snd_576_);
v___x_581_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_mkTypeSnd(v_fst_575_);
if (v_isShared_579_ == 0)
{
lean_ctor_set(v___x_578_, 1, v___x_580_);
lean_ctor_set(v___x_578_, 0, v___x_581_);
v___x_583_ = v___x_578_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v___x_581_);
lean_ctor_set(v_reuseFailAlloc_587_, 1, v___x_580_);
v___x_583_ = v_reuseFailAlloc_587_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_584_ = lean_unsigned_to_nat(1u);
v___x_585_ = lean_nat_add(v_a_572_, v___x_584_);
lean_dec(v_a_572_);
v_a_572_ = v___x_585_;
v_b_573_ = v___x_583_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_proj_spec__0___redArg___boxed(lean_object* v_upperBound_589_, lean_object* v_a_590_, lean_object* v_b_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_proj_spec__0___redArg(v_upperBound_589_, v_a_590_, v_b_591_);
lean_dec(v_upperBound_589_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_proj(lean_object* v_n_593_, lean_object* v_i_594_, lean_object* v_t_595_, lean_object* v_e_596_){
_start:
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v_fst_600_; lean_object* v_snd_601_; lean_object* v___x_602_; lean_object* v___x_603_; uint8_t v___x_604_; 
v___x_597_ = lean_unsigned_to_nat(0u);
v___x_598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_598_, 0, v_t_595_);
lean_ctor_set(v___x_598_, 1, v_e_596_);
v___x_599_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_proj_spec__0___redArg(v_i_594_, v___x_597_, v___x_598_);
v_fst_600_ = lean_ctor_get(v___x_599_, 0);
lean_inc(v_fst_600_);
v_snd_601_ = lean_ctor_get(v___x_599_, 1);
lean_inc(v_snd_601_);
lean_dec_ref(v___x_599_);
v___x_602_ = lean_unsigned_to_nat(1u);
v___x_603_ = lean_nat_add(v_i_594_, v___x_602_);
v___x_604_ = lean_nat_dec_lt(v___x_603_, v_n_593_);
lean_dec(v___x_603_);
if (v___x_604_ == 0)
{
lean_dec(v_fst_600_);
return v_snd_601_;
}
else
{
lean_object* v___x_605_; 
v___x_605_ = l_Lean_Meta_mkPProdFst(v_fst_600_, v_snd_601_);
return v___x_605_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_proj___boxed(lean_object* v_n_606_, lean_object* v_i_607_, lean_object* v_t_608_, lean_object* v_e_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l_Lean_Meta_PProdN_proj(v_n_606_, v_i_607_, v_t_608_, v_e_609_);
lean_dec(v_i_607_);
lean_dec(v_n_606_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_proj_spec__0(lean_object* v_upperBound_611_, lean_object* v_inst_612_, lean_object* v_R_613_, lean_object* v_a_614_, lean_object* v_b_615_, lean_object* v_c_616_){
_start:
{
lean_object* v___x_617_; 
v___x_617_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_proj_spec__0___redArg(v_upperBound_611_, v_a_614_, v_b_615_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_proj_spec__0___boxed(lean_object* v_upperBound_618_, lean_object* v_inst_619_, lean_object* v_R_620_, lean_object* v_a_621_, lean_object* v_b_622_, lean_object* v_c_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_proj_spec__0(v_upperBound_618_, v_inst_619_, v_R_620_, v_a_621_, v_b_622_, v_c_623_);
lean_dec(v_upperBound_618_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_projs___lam__0(lean_object* v_n_625_, lean_object* v_t_626_, lean_object* v_e_627_, lean_object* v_i_628_){
_start:
{
lean_object* v___x_629_; 
v___x_629_ = l_Lean_Meta_PProdN_proj(v_n_625_, v_i_628_, v_t_626_, v_e_627_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_projs___lam__0___boxed(lean_object* v_n_630_, lean_object* v_t_631_, lean_object* v_e_632_, lean_object* v_i_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_Lean_Meta_PProdN_projs___lam__0(v_n_630_, v_t_631_, v_e_632_, v_i_633_);
lean_dec(v_i_633_);
lean_dec(v_n_630_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_projs(lean_object* v_n_635_, lean_object* v_t_636_, lean_object* v_e_637_){
_start:
{
lean_object* v___f_638_; lean_object* v___x_639_; 
lean_inc(v_n_635_);
v___f_638_ = lean_alloc_closure((void*)(l_Lean_Meta_PProdN_projs___lam__0___boxed), 4, 3);
lean_closure_set(v___f_638_, 0, v_n_635_);
lean_closure_set(v___f_638_, 1, v_t_636_);
lean_closure_set(v___f_638_, 2, v_e_637_);
v___x_639_ = l_Array_ofFn___redArg(v_n_635_, v___f_638_);
return v___x_639_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_projM_spec__0___redArg(lean_object* v_upperBound_640_, lean_object* v_a_641_, lean_object* v_b_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_){
_start:
{
uint8_t v___x_648_; 
v___x_648_ = lean_nat_dec_lt(v_a_641_, v_upperBound_640_);
if (v___x_648_ == 0)
{
lean_object* v___x_649_; 
lean_dec(v_a_641_);
v___x_649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_649_, 0, v_b_642_);
return v___x_649_;
}
else
{
lean_object* v___x_650_; 
v___x_650_ = l_Lean_Meta_mkPProdSndM(v_b_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_);
if (lean_obj_tag(v___x_650_) == 0)
{
lean_object* v_a_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
v_a_651_ = lean_ctor_get(v___x_650_, 0);
lean_inc(v_a_651_);
lean_dec_ref_known(v___x_650_, 1);
v___x_652_ = lean_unsigned_to_nat(1u);
v___x_653_ = lean_nat_add(v_a_641_, v___x_652_);
lean_dec(v_a_641_);
v_a_641_ = v___x_653_;
v_b_642_ = v_a_651_;
goto _start;
}
else
{
lean_dec(v_a_641_);
return v___x_650_;
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_projM_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_640_ = stack[0].m_obj;
lean_object* v_a_641_ = stack[1].m_obj;
lean_object* v_b_642_ = stack[2].m_obj;
lean_object* v___y_643_ = stack[3].m_obj;
lean_object* v___y_644_ = stack[4].m_obj;
lean_object* v___y_645_ = stack[5].m_obj;
lean_object* v___y_646_ = stack[6].m_obj;
lean_object* v_res_655_;
v_res_655_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_projM_spec__0___redArg(v_upperBound_640_, v_a_641_, v_b_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_);
stack->m_obj
 = v_res_655_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_projM_spec__0___redArg___boxed(lean_object* v_upperBound_656_, lean_object* v_a_657_, lean_object* v_b_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_projM_spec__0___redArg(v_upperBound_656_, v_a_657_, v_b_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_);
lean_dec(v___y_662_);
lean_dec_ref(v___y_661_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v_upperBound_656_);
return v_res_664_;
}
}
lean_object* l_Lean_Meta_PProdN_projM(lean_object* v_n_665_, lean_object* v_i_666_, lean_object* v_e_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_){
_start:
{
lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_673_ = lean_unsigned_to_nat(0u);
v___x_674_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_projM_spec__0___redArg(v_i_666_, v___x_673_, v_e_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_);
if (lean_obj_tag(v___x_674_) == 0)
{
lean_object* v_a_675_; lean_object* v___x_676_; lean_object* v___x_677_; uint8_t v___x_678_; 
v_a_675_ = lean_ctor_get(v___x_674_, 0);
v___x_676_ = lean_unsigned_to_nat(1u);
v___x_677_ = lean_nat_add(v_i_666_, v___x_676_);
v___x_678_ = lean_nat_dec_lt(v___x_677_, v_n_665_);
lean_dec(v___x_677_);
if (v___x_678_ == 0)
{
return v___x_674_;
}
else
{
lean_object* v___x_679_; 
lean_inc(v_a_675_);
lean_dec_ref_known(v___x_674_, 1);
v___x_679_ = l_Lean_Meta_mkPProdFstM(v_a_675_, v_a_668_, v_a_669_, v_a_670_, v_a_671_);
return v___x_679_;
}
}
else
{
return v___x_674_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_PProdN_projM_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_665_ = stack[0].m_obj;
lean_object* v_i_666_ = stack[1].m_obj;
lean_object* v_e_667_ = stack[2].m_obj;
lean_object* v_a_668_ = stack[3].m_obj;
lean_object* v_a_669_ = stack[4].m_obj;
lean_object* v_a_670_ = stack[5].m_obj;
lean_object* v_a_671_ = stack[6].m_obj;
lean_object* v_res_680_;
v_res_680_ = l_Lean_Meta_PProdN_projM(v_n_665_, v_i_666_, v_e_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_);
stack->m_obj
 = v_res_680_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_projM___boxed(lean_object* v_n_681_, lean_object* v_i_682_, lean_object* v_e_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l_Lean_Meta_PProdN_projM(v_n_681_, v_i_682_, v_e_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_);
lean_dec(v_a_687_);
lean_dec_ref(v_a_686_);
lean_dec(v_a_685_);
lean_dec_ref(v_a_684_);
lean_dec(v_i_682_);
lean_dec(v_n_681_);
return v_res_689_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_projM_spec__0(lean_object* v_upperBound_690_, lean_object* v_inst_691_, lean_object* v_R_692_, lean_object* v_a_693_, lean_object* v_b_694_, lean_object* v_c_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_){
_start:
{
lean_object* v___x_701_; 
v___x_701_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_projM_spec__0___redArg(v_upperBound_690_, v_a_693_, v_b_694_, v___y_696_, v___y_697_, v___y_698_, v___y_699_);
return v___x_701_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_projM_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_690_ = stack[0].m_obj;
lean_object* v_a_693_ = stack[3].m_obj;
lean_object* v_b_694_ = stack[4].m_obj;
lean_object* v___y_696_ = stack[6].m_obj;
lean_object* v___y_697_ = stack[7].m_obj;
lean_object* v___y_698_ = stack[8].m_obj;
lean_object* v___y_699_ = stack[9].m_obj;
lean_object* v_res_702_;
v_res_702_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_projM_spec__0(v_upperBound_690_, lean_box(0), lean_box(0), v_a_693_, v_b_694_, lean_box(0), v___y_696_, v___y_697_, v___y_698_, v___y_699_);
stack->m_obj
 = v_res_702_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_projM_spec__0___boxed(lean_object* v_upperBound_703_, lean_object* v_inst_704_, lean_object* v_R_705_, lean_object* v_a_706_, lean_object* v_b_707_, lean_object* v_c_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_){
_start:
{
lean_object* v_res_714_; 
v_res_714_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_projM_spec__0(v_upperBound_703_, v_inst_704_, v_R_705_, v_a_706_, v_b_707_, v_c_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_);
lean_dec(v___y_712_);
lean_dec_ref(v___y_711_);
lean_dec(v___y_710_);
lean_dec_ref(v___y_709_);
lean_dec(v_upperBound_703_);
return v_res_714_;
}
}
lean_object* l_panic___at___00Lean_Meta_PProdN_packLambdas_spec__0(lean_object* v_msg_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_){
_start:
{
lean_object* v___f_721_; lean_object* v___x_336__overap_722_; lean_object* v___x_723_; 
v___f_721_ = ((lean_object*)(l_Lean_Meta_PProdN_genMk___redArg___closed__6));
v___x_336__overap_722_ = lean_panic_fn_borrowed(v___f_721_, v_msg_715_);
lean_inc(v___y_719_);
lean_inc_ref(v___y_718_);
lean_inc(v___y_717_);
lean_inc_ref(v___y_716_);
v___x_723_ = lean_apply_5(v___x_336__overap_722_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, lean_box(0));
return v___x_723_;
}
}
LEAN_EXPORT void l_panic___at___00Lean_Meta_PProdN_packLambdas_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_715_ = stack[0].m_obj;
lean_object* v___y_716_ = stack[1].m_obj;
lean_object* v___y_717_ = stack[2].m_obj;
lean_object* v___y_718_ = stack[3].m_obj;
lean_object* v___y_719_ = stack[4].m_obj;
lean_object* v_res_724_;
v_res_724_ = l_panic___at___00Lean_Meta_PProdN_packLambdas_spec__0(v_msg_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_);
stack->m_obj
 = v_res_724_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_PProdN_packLambdas_spec__0___boxed(lean_object* v_msg_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = l_panic___at___00Lean_Meta_PProdN_packLambdas_spec__0(v_msg_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_);
lean_dec(v___y_729_);
lean_dec_ref(v___y_728_);
lean_dec(v___y_727_);
lean_dec_ref(v___y_726_);
return v_res_731_;
}
}
lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___redArg___lam__0(lean_object* v_k_732_, lean_object* v_b_733_, lean_object* v_c_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
lean_object* v___x_740_; 
lean_inc(v___y_738_);
lean_inc_ref(v___y_737_);
lean_inc(v___y_736_);
lean_inc_ref(v___y_735_);
v___x_740_ = lean_apply_7(v_k_732_, v_b_733_, v_c_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, lean_box(0));
return v___x_740_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_732_ = stack[0].m_obj;
lean_object* v_b_733_ = stack[1].m_obj;
lean_object* v_c_734_ = stack[2].m_obj;
lean_object* v___y_735_ = stack[3].m_obj;
lean_object* v___y_736_ = stack[4].m_obj;
lean_object* v___y_737_ = stack[5].m_obj;
lean_object* v___y_738_ = stack[6].m_obj;
lean_object* v_res_741_;
v_res_741_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___redArg___lam__0(v_k_732_, v_b_733_, v_c_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_);
stack->m_obj
 = v_res_741_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___redArg___lam__0___boxed(lean_object* v_k_742_, lean_object* v_b_743_, lean_object* v_c_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___redArg___lam__0(v_k_742_, v_b_743_, v_c_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_);
lean_dec(v___y_748_);
lean_dec_ref(v___y_747_);
lean_dec(v___y_746_);
lean_dec_ref(v___y_745_);
return v_res_750_;
}
}
lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___redArg(lean_object* v_type_751_, lean_object* v_k_752_, uint8_t v_cleanupAnnotations_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_){
_start:
{
lean_object* v___f_759_; uint8_t v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; 
v___f_759_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_759_, 0, v_k_752_);
v___x_760_ = 0;
v___x_761_ = lean_box(0);
v___x_762_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_760_, v___x_761_, v_type_751_, v___f_759_, v_cleanupAnnotations_753_, v___x_760_, v___y_754_, v___y_755_, v___y_756_, v___y_757_);
if (lean_obj_tag(v___x_762_) == 0)
{
lean_object* v_a_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_770_; 
v_a_763_ = lean_ctor_get(v___x_762_, 0);
v_isSharedCheck_770_ = !lean_is_exclusive(v___x_762_);
if (v_isSharedCheck_770_ == 0)
{
v___x_765_ = v___x_762_;
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_a_763_);
lean_dec(v___x_762_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_768_; 
if (v_isShared_766_ == 0)
{
v___x_768_ = v___x_765_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v_a_763_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
else
{
lean_object* v_a_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_778_; 
v_a_771_ = lean_ctor_get(v___x_762_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_762_);
if (v_isSharedCheck_778_ == 0)
{
v___x_773_ = v___x_762_;
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_a_771_);
lean_dec(v___x_762_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_776_; 
if (v_isShared_774_ == 0)
{
v___x_776_ = v___x_773_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_a_771_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_751_ = stack[0].m_obj;
lean_object* v_k_752_ = stack[1].m_obj;
uint8_t v_cleanupAnnotations_753_ = stack[2].m_num;
lean_object* v___y_754_ = stack[3].m_obj;
lean_object* v___y_755_ = stack[4].m_obj;
lean_object* v___y_756_ = stack[5].m_obj;
lean_object* v___y_757_ = stack[6].m_obj;
lean_object* v_res_779_;
v_res_779_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___redArg(v_type_751_, v_k_752_, v_cleanupAnnotations_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_);
stack->m_obj
 = v_res_779_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___redArg___boxed(lean_object* v_type_780_, lean_object* v_k_781_, lean_object* v_cleanupAnnotations_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_788_; lean_object* v_res_789_; 
v_cleanupAnnotations_boxed_788_ = lean_unbox(v_cleanupAnnotations_782_);
v_res_789_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___redArg(v_type_780_, v_k_781_, v_cleanupAnnotations_boxed_788_, v___y_783_, v___y_784_, v___y_785_, v___y_786_);
lean_dec(v___y_786_);
lean_dec_ref(v___y_785_);
lean_dec(v___y_784_);
lean_dec_ref(v___y_783_);
return v_res_789_;
}
}
lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2(lean_object* v_00_u03b1_790_, lean_object* v_type_791_, lean_object* v_k_792_, uint8_t v_cleanupAnnotations_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_){
_start:
{
lean_object* v___x_799_; 
v___x_799_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___redArg(v_type_791_, v_k_792_, v_cleanupAnnotations_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_);
return v___x_799_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_791_ = stack[1].m_obj;
lean_object* v_k_792_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_793_ = stack[3].m_num;
lean_object* v___y_794_ = stack[4].m_obj;
lean_object* v___y_795_ = stack[5].m_obj;
lean_object* v___y_796_ = stack[6].m_obj;
lean_object* v___y_797_ = stack[7].m_obj;
lean_object* v_res_800_;
v_res_800_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2(lean_box(0), v_type_791_, v_k_792_, v_cleanupAnnotations_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_);
stack->m_obj
 = v_res_800_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___boxed(lean_object* v_00_u03b1_801_, lean_object* v_type_802_, lean_object* v_k_803_, lean_object* v_cleanupAnnotations_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_810_; lean_object* v_res_811_; 
v_cleanupAnnotations_boxed_810_ = lean_unbox(v_cleanupAnnotations_804_);
v_res_811_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2(v_00_u03b1_801_, v_type_802_, v_k_803_, v_cleanupAnnotations_boxed_810_, v___y_805_, v___y_806_, v___y_807_, v___y_808_);
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_805_);
return v_res_811_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_PProdN_packLambdas_spec__1(lean_object* v_xs_812_, size_t v_sz_813_, size_t v_i_814_, lean_object* v_bs_815_){
_start:
{
uint8_t v___x_816_; 
v___x_816_ = lean_usize_dec_lt(v_i_814_, v_sz_813_);
if (v___x_816_ == 0)
{
lean_dec_ref(v_xs_812_);
return v_bs_815_;
}
else
{
lean_object* v_v_817_; lean_object* v___x_818_; lean_object* v_bs_x27_819_; lean_object* v___x_820_; size_t v___x_821_; size_t v___x_822_; lean_object* v___x_823_; 
v_v_817_ = lean_array_uget(v_bs_815_, v_i_814_);
v___x_818_ = lean_unsigned_to_nat(0u);
v_bs_x27_819_ = lean_array_uset(v_bs_815_, v_i_814_, v___x_818_);
lean_inc_ref(v_xs_812_);
v___x_820_ = l_Lean_Expr_beta(v_v_817_, v_xs_812_);
v___x_821_ = ((size_t)1ULL);
v___x_822_ = lean_usize_add(v_i_814_, v___x_821_);
v___x_823_ = lean_array_uset(v_bs_x27_819_, v_i_814_, v___x_820_);
v_i_814_ = v___x_822_;
v_bs_815_ = v___x_823_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_PProdN_packLambdas_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_812_ = stack[0].m_obj;
size_t v_sz_813_ = stack[1].m_num;
size_t v_i_814_ = stack[2].m_num;
lean_object* v_bs_815_ = stack[3].m_obj;
lean_object* v_res_825_;
v_res_825_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_PProdN_packLambdas_spec__1(v_xs_812_, v_sz_813_, v_i_814_, v_bs_815_);
stack->m_obj
 = v_res_825_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_PProdN_packLambdas_spec__1___boxed(lean_object* v_xs_826_, lean_object* v_sz_827_, lean_object* v_i_828_, lean_object* v_bs_829_){
_start:
{
size_t v_sz_boxed_830_; size_t v_i_boxed_831_; lean_object* v_res_832_; 
v_sz_boxed_830_ = lean_unbox_usize(v_sz_827_);
lean_dec(v_sz_827_);
v_i_boxed_831_ = lean_unbox_usize(v_i_828_);
lean_dec(v_i_828_);
v_res_832_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_PProdN_packLambdas_spec__1(v_xs_826_, v_sz_boxed_830_, v_i_boxed_831_, v_bs_829_);
return v_res_832_;
}
}
static lean_object* _init_l_Lean_Meta_PProdN_packLambdas___lam__0___closed__2(void){
_start:
{
lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; 
v___x_835_ = ((lean_object*)(l_Lean_Meta_PProdN_packLambdas___lam__0___closed__1));
v___x_836_ = lean_unsigned_to_nat(4u);
v___x_837_ = lean_unsigned_to_nat(175u);
v___x_838_ = ((lean_object*)(l_Lean_Meta_PProdN_packLambdas___lam__0___closed__0));
v___x_839_ = ((lean_object*)(l_Lean_Meta_mkPProdFst___closed__0));
v___x_840_ = l_mkPanicMessageWithDecl(v___x_839_, v___x_838_, v___x_837_, v___x_836_, v___x_835_);
return v___x_840_;
}
}
lean_object* l_Lean_Meta_PProdN_packLambdas___lam__0(lean_object* v_es_841_, uint8_t v___x_842_, lean_object* v_xs_843_, lean_object* v_sort_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_){
_start:
{
uint8_t v___x_850_; 
v___x_850_ = l_Lean_Expr_isSort(v_sort_844_);
if (v___x_850_ == 0)
{
lean_object* v___x_851_; lean_object* v___x_852_; 
lean_dec_ref(v_xs_843_);
lean_dec_ref(v_es_841_);
v___x_851_ = lean_obj_once(&l_Lean_Meta_PProdN_packLambdas___lam__0___closed__2, &l_Lean_Meta_PProdN_packLambdas___lam__0___closed__2_once, _init_l_Lean_Meta_PProdN_packLambdas___lam__0___closed__2);
v___x_852_ = l_panic___at___00Lean_Meta_PProdN_packLambdas_spec__0(v___x_851_, v___y_845_, v___y_846_, v___y_847_, v___y_848_);
return v___x_852_;
}
else
{
size_t v_sz_853_; size_t v___x_854_; lean_object* v_es_x27_855_; lean_object* v___x_856_; lean_object* v___x_857_; 
v_sz_853_ = lean_array_size(v_es_841_);
v___x_854_ = ((size_t)0ULL);
lean_inc_ref(v_xs_843_);
v_es_x27_855_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_PProdN_packLambdas_spec__1(v_xs_843_, v_sz_853_, v___x_854_, v_es_841_);
v___x_856_ = l_Lean_Expr_sortLevel_x21(v_sort_844_);
v___x_857_ = l_Lean_Meta_PProdN_pack(v___x_856_, v_es_x27_855_, v___y_845_, v___y_846_, v___y_847_, v___y_848_);
if (lean_obj_tag(v___x_857_) == 0)
{
lean_object* v_a_858_; uint8_t v___x_859_; lean_object* v___x_860_; 
v_a_858_ = lean_ctor_get(v___x_857_, 0);
lean_inc(v_a_858_);
lean_dec_ref_known(v___x_857_, 1);
v___x_859_ = 1;
v___x_860_ = l_Lean_Meta_mkLambdaFVars(v_xs_843_, v_a_858_, v___x_842_, v___x_850_, v___x_842_, v___x_850_, v___x_859_, v___y_845_, v___y_846_, v___y_847_, v___y_848_);
lean_dec_ref(v_xs_843_);
return v___x_860_;
}
else
{
lean_dec_ref(v_xs_843_);
return v___x_857_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_PProdN_packLambdas___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_es_841_ = stack[0].m_obj;
uint8_t v___x_842_ = stack[1].m_num;
lean_object* v_xs_843_ = stack[2].m_obj;
lean_object* v_sort_844_ = stack[3].m_obj;
lean_object* v___y_845_ = stack[4].m_obj;
lean_object* v___y_846_ = stack[5].m_obj;
lean_object* v___y_847_ = stack[6].m_obj;
lean_object* v___y_848_ = stack[7].m_obj;
lean_object* v_res_861_;
v_res_861_ = l_Lean_Meta_PProdN_packLambdas___lam__0(v_es_841_, v___x_842_, v_xs_843_, v_sort_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_);
stack->m_obj
 = v_res_861_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_packLambdas___lam__0___boxed(lean_object* v_es_862_, lean_object* v___x_863_, lean_object* v_xs_864_, lean_object* v_sort_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_){
_start:
{
uint8_t v___x_1007__boxed_871_; lean_object* v_res_872_; 
v___x_1007__boxed_871_ = lean_unbox(v___x_863_);
v_res_872_ = l_Lean_Meta_PProdN_packLambdas___lam__0(v_es_862_, v___x_1007__boxed_871_, v_xs_864_, v_sort_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_);
lean_dec(v___y_869_);
lean_dec_ref(v___y_868_);
lean_dec(v___y_867_);
lean_dec_ref(v___y_866_);
lean_dec_ref(v_sort_865_);
return v_res_872_;
}
}
lean_object* l_Lean_Meta_PProdN_packLambdas(lean_object* v_type_873_, lean_object* v_es_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_){
_start:
{
lean_object* v___x_880_; lean_object* v___x_881_; uint8_t v___x_882_; 
v___x_880_ = lean_array_get_size(v_es_874_);
v___x_881_ = lean_unsigned_to_nat(1u);
v___x_882_ = lean_nat_dec_eq(v___x_880_, v___x_881_);
if (v___x_882_ == 0)
{
lean_object* v___x_883_; lean_object* v___f_884_; lean_object* v___x_885_; 
v___x_883_ = lean_box(v___x_882_);
v___f_884_ = lean_alloc_closure((void*)(l_Lean_Meta_PProdN_packLambdas___lam__0___boxed), 9, 2);
lean_closure_set(v___f_884_, 0, v_es_874_);
lean_closure_set(v___f_884_, 1, v___x_883_);
v___x_885_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___redArg(v_type_873_, v___f_884_, v___x_882_, v_a_875_, v_a_876_, v_a_877_, v_a_878_);
return v___x_885_;
}
else
{
lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; 
lean_dec_ref(v_type_873_);
v___x_886_ = lean_unsigned_to_nat(0u);
v___x_887_ = lean_array_fget(v_es_874_, v___x_886_);
lean_dec_ref(v_es_874_);
v___x_888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_888_, 0, v___x_887_);
return v___x_888_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_PProdN_packLambdas_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_873_ = stack[0].m_obj;
lean_object* v_es_874_ = stack[1].m_obj;
lean_object* v_a_875_ = stack[2].m_obj;
lean_object* v_a_876_ = stack[3].m_obj;
lean_object* v_a_877_ = stack[4].m_obj;
lean_object* v_a_878_ = stack[5].m_obj;
lean_object* v_res_889_;
v_res_889_ = l_Lean_Meta_PProdN_packLambdas(v_type_873_, v_es_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_);
stack->m_obj
 = v_res_889_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_packLambdas___boxed(lean_object* v_type_890_, lean_object* v_es_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_){
_start:
{
lean_object* v_res_897_; 
v_res_897_ = l_Lean_Meta_PProdN_packLambdas(v_type_890_, v_es_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_);
lean_dec(v_a_895_);
lean_dec_ref(v_a_894_);
lean_dec(v_a_893_);
lean_dec_ref(v_a_892_);
return v_res_897_;
}
}
lean_object* l_Lean_Meta_PProdN_mkLambdas___lam__0(lean_object* v_es_898_, uint8_t v___x_899_, lean_object* v_xs_900_, lean_object* v_body_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
lean_object* v___x_907_; 
v___x_907_ = l_Lean_Meta_getLevel(v_body_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_);
if (lean_obj_tag(v___x_907_) == 0)
{
lean_object* v_a_908_; size_t v_sz_909_; size_t v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
v_a_908_ = lean_ctor_get(v___x_907_, 0);
lean_inc(v_a_908_);
lean_dec_ref_known(v___x_907_, 1);
v_sz_909_ = lean_array_size(v_es_898_);
v___x_910_ = ((size_t)0ULL);
lean_inc_ref(v_xs_900_);
v___x_911_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_PProdN_packLambdas_spec__1(v_xs_900_, v_sz_909_, v___x_910_, v_es_898_);
v___x_912_ = l_Lean_Meta_PProdN_mk(v_a_908_, v___x_911_, v___y_902_, v___y_903_, v___y_904_, v___y_905_);
if (lean_obj_tag(v___x_912_) == 0)
{
lean_object* v_a_913_; uint8_t v___x_914_; uint8_t v___x_915_; lean_object* v___x_916_; 
v_a_913_ = lean_ctor_get(v___x_912_, 0);
lean_inc(v_a_913_);
lean_dec_ref_known(v___x_912_, 1);
v___x_914_ = 1;
v___x_915_ = 1;
v___x_916_ = l_Lean_Meta_mkLambdaFVars(v_xs_900_, v_a_913_, v___x_899_, v___x_914_, v___x_899_, v___x_914_, v___x_915_, v___y_902_, v___y_903_, v___y_904_, v___y_905_);
lean_dec_ref(v_xs_900_);
return v___x_916_;
}
else
{
lean_dec_ref(v_xs_900_);
return v___x_912_;
}
}
else
{
lean_object* v_a_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_924_; 
lean_dec_ref(v_xs_900_);
lean_dec_ref(v_es_898_);
v_a_917_ = lean_ctor_get(v___x_907_, 0);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_907_);
if (v_isSharedCheck_924_ == 0)
{
v___x_919_ = v___x_907_;
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_a_917_);
lean_dec(v___x_907_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_922_; 
if (v_isShared_920_ == 0)
{
v___x_922_ = v___x_919_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v_a_917_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_PProdN_mkLambdas___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_es_898_ = stack[0].m_obj;
uint8_t v___x_899_ = stack[1].m_num;
lean_object* v_xs_900_ = stack[2].m_obj;
lean_object* v_body_901_ = stack[3].m_obj;
lean_object* v___y_902_ = stack[4].m_obj;
lean_object* v___y_903_ = stack[5].m_obj;
lean_object* v___y_904_ = stack[6].m_obj;
lean_object* v___y_905_ = stack[7].m_obj;
lean_object* v_res_925_;
v_res_925_ = l_Lean_Meta_PProdN_mkLambdas___lam__0(v_es_898_, v___x_899_, v_xs_900_, v_body_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_);
stack->m_obj
 = v_res_925_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_mkLambdas___lam__0___boxed(lean_object* v_es_926_, lean_object* v___x_927_, lean_object* v_xs_928_, lean_object* v_body_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_){
_start:
{
uint8_t v___x_364__boxed_935_; lean_object* v_res_936_; 
v___x_364__boxed_935_ = lean_unbox(v___x_927_);
v_res_936_ = l_Lean_Meta_PProdN_mkLambdas___lam__0(v_es_926_, v___x_364__boxed_935_, v_xs_928_, v_body_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
lean_dec(v___y_931_);
lean_dec_ref(v___y_930_);
return v_res_936_;
}
}
lean_object* l_Lean_Meta_PProdN_mkLambdas(lean_object* v_type_937_, lean_object* v_es_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_){
_start:
{
lean_object* v___x_944_; lean_object* v___x_945_; uint8_t v___x_946_; 
v___x_944_ = lean_array_get_size(v_es_938_);
v___x_945_ = lean_unsigned_to_nat(1u);
v___x_946_ = lean_nat_dec_eq(v___x_944_, v___x_945_);
if (v___x_946_ == 0)
{
lean_object* v___x_947_; lean_object* v___f_948_; lean_object* v___x_949_; 
v___x_947_ = lean_box(v___x_946_);
v___f_948_ = lean_alloc_closure((void*)(l_Lean_Meta_PProdN_mkLambdas___lam__0___boxed), 9, 2);
lean_closure_set(v___f_948_, 0, v_es_938_);
lean_closure_set(v___f_948_, 1, v___x_947_);
v___x_949_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___redArg(v_type_937_, v___f_948_, v___x_946_, v_a_939_, v_a_940_, v_a_941_, v_a_942_);
return v___x_949_;
}
else
{
lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; 
lean_dec_ref(v_type_937_);
v___x_950_ = lean_unsigned_to_nat(0u);
v___x_951_ = lean_array_fget(v_es_938_, v___x_950_);
lean_dec_ref(v_es_938_);
v___x_952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_952_, 0, v___x_951_);
return v___x_952_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_PProdN_mkLambdas_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_937_ = stack[0].m_obj;
lean_object* v_es_938_ = stack[1].m_obj;
lean_object* v_a_939_ = stack[2].m_obj;
lean_object* v_a_940_ = stack[3].m_obj;
lean_object* v_a_941_ = stack[4].m_obj;
lean_object* v_a_942_ = stack[5].m_obj;
lean_object* v_res_953_;
v_res_953_ = l_Lean_Meta_PProdN_mkLambdas(v_type_937_, v_es_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_);
stack->m_obj
 = v_res_953_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_mkLambdas___boxed(lean_object* v_type_954_, lean_object* v_es_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l_Lean_Meta_PProdN_mkLambdas(v_type_954_, v_es_955_, v_a_956_, v_a_957_, v_a_958_, v_a_959_);
lean_dec(v_a_959_);
lean_dec_ref(v_a_958_);
lean_dec(v_a_957_);
lean_dec_ref(v_a_956_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_stripProjs(lean_object* v_e_962_){
_start:
{
if (lean_obj_tag(v_e_962_) == 11)
{
lean_object* v_typeName_963_; 
v_typeName_963_ = lean_ctor_get(v_e_962_, 0);
if (lean_obj_tag(v_typeName_963_) == 1)
{
lean_object* v_pre_964_; 
v_pre_964_ = lean_ctor_get(v_typeName_963_, 0);
if (lean_obj_tag(v_pre_964_) == 0)
{
lean_object* v_struct_965_; lean_object* v_str_966_; lean_object* v___x_967_; uint8_t v___x_968_; 
v_struct_965_ = lean_ctor_get(v_e_962_, 2);
v_str_966_ = lean_ctor_get(v_typeName_963_, 1);
v___x_967_ = ((lean_object*)(l_Lean_Meta_mkPProd___closed__0));
v___x_968_ = lean_string_dec_eq(v_str_966_, v___x_967_);
if (v___x_968_ == 0)
{
lean_object* v___x_969_; uint8_t v___x_970_; 
v___x_969_ = ((lean_object*)(l_Lean_Meta_mkPProd___closed__2));
v___x_970_ = lean_string_dec_eq(v_str_966_, v___x_969_);
if (v___x_970_ == 0)
{
lean_inc_ref(v_e_962_);
return v_e_962_;
}
else
{
v_e_962_ = v_struct_965_;
goto _start;
}
}
else
{
v_e_962_ = v_struct_965_;
goto _start;
}
}
else
{
lean_inc_ref(v_e_962_);
return v_e_962_;
}
}
else
{
lean_inc_ref(v_e_962_);
return v_e_962_;
}
}
else
{
lean_inc_ref(v_e_962_);
return v_e_962_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_stripProjs___boxed(lean_object* v_e_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l_Lean_Meta_PProdN_stripProjs(v_e_973_);
lean_dec_ref(v_e_973_);
return v_res_974_;
}
}
lean_object* l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___redArg(lean_object* v_e_977_, lean_object* v_i_978_){
_start:
{
uint8_t v___y_981_; lean_object* v___x_995_; lean_object* v___x_996_; uint8_t v___x_997_; 
v___x_995_ = ((lean_object*)(l_Lean_Meta_mkPProdMk___closed__1));
v___x_996_ = lean_unsigned_to_nat(4u);
v___x_997_ = l_Lean_Expr_isAppOfArity(v_e_977_, v___x_995_, v___x_996_);
if (v___x_997_ == 0)
{
lean_object* v___x_998_; lean_object* v___x_999_; uint8_t v___x_1000_; 
v___x_998_ = ((lean_object*)(l_Lean_Meta_mkPProdMk___closed__3));
v___x_999_ = lean_unsigned_to_nat(2u);
v___x_1000_ = l_Lean_Expr_isAppOfArity(v_e_977_, v___x_998_, v___x_999_);
v___y_981_ = v___x_1000_;
goto v___jp_980_;
}
else
{
v___y_981_ = v___x_997_;
goto v___jp_980_;
}
v___jp_980_:
{
if (v___y_981_ == 0)
{
lean_object* v___x_982_; lean_object* v___x_983_; 
v___x_982_ = ((lean_object*)(l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___redArg___closed__0));
v___x_983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_983_, 0, v___x_982_);
return v___x_983_;
}
else
{
lean_object* v___x_984_; uint8_t v___x_985_; 
v___x_984_ = lean_unsigned_to_nat(0u);
v___x_985_ = lean_nat_dec_eq(v_i_978_, v___x_984_);
if (v___x_985_ == 0)
{
lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_986_ = l_Lean_Expr_appArg_x21(v_e_977_);
v___x_987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_987_, 0, v___x_986_);
v___x_988_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_988_, 0, v___x_987_);
v___x_989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_989_, 0, v___x_988_);
return v___x_989_;
}
else
{
lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_990_ = l_Lean_Expr_appFn_x21(v_e_977_);
v___x_991_ = l_Lean_Expr_appArg_x21(v___x_990_);
lean_dec_ref(v___x_990_);
v___x_992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_992_, 0, v___x_991_);
v___x_993_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_993_, 0, v___x_992_);
v___x_994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_994_, 0, v___x_993_);
return v___x_994_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_977_ = stack[0].m_obj;
lean_object* v_i_978_ = stack[1].m_obj;
lean_object* v_res_1001_;
v_res_1001_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___redArg(v_e_977_, v_i_978_);
stack->m_obj
 = v_res_1001_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___redArg___boxed(lean_object* v_e_1002_, lean_object* v_i_1003_, lean_object* v_a_1004_){
_start:
{
lean_object* v_res_1005_; 
v_res_1005_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___redArg(v_e_1002_, v_i_1003_);
lean_dec(v_i_1003_);
lean_dec_ref(v_e_1002_);
return v_res_1005_;
}
}
lean_object* l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce(lean_object* v_e_1006_, lean_object* v_i_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_){
_start:
{
lean_object* v___x_1013_; 
v___x_1013_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___redArg(v_e_1006_, v_i_1007_);
return v___x_1013_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1006_ = stack[0].m_obj;
lean_object* v_i_1007_ = stack[1].m_obj;
lean_object* v_a_1008_ = stack[2].m_obj;
lean_object* v_a_1009_ = stack[3].m_obj;
lean_object* v_a_1010_ = stack[4].m_obj;
lean_object* v_a_1011_ = stack[5].m_obj;
lean_object* v_res_1014_;
v_res_1014_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce(v_e_1006_, v_i_1007_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_);
stack->m_obj
 = v_res_1014_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___boxed(lean_object* v_e_1015_, lean_object* v_i_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_){
_start:
{
lean_object* v_res_1022_; 
v_res_1022_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce(v_e_1015_, v_i_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_);
lean_dec(v_a_1020_);
lean_dec_ref(v_a_1019_);
lean_dec(v_a_1018_);
lean_dec_ref(v_a_1017_);
lean_dec(v_i_1016_);
lean_dec_ref(v_e_1015_);
return v_res_1022_;
}
}
lean_object* l_Lean_Meta_PProdN_reduceProjs___lam__0(lean_object* v_x_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_){
_start:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1029_ = ((lean_object*)(l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___redArg___closed__0));
v___x_1030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1029_);
return v___x_1030_;
}
}
LEAN_EXPORT void l_Lean_Meta_PProdN_reduceProjs___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1023_ = stack[0].m_obj;
lean_object* v___y_1024_ = stack[1].m_obj;
lean_object* v___y_1025_ = stack[2].m_obj;
lean_object* v___y_1026_ = stack[3].m_obj;
lean_object* v___y_1027_ = stack[4].m_obj;
lean_object* v_res_1031_;
v_res_1031_ = l_Lean_Meta_PProdN_reduceProjs___lam__0(v_x_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_);
stack->m_obj
 = v_res_1031_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_reduceProjs___lam__0___boxed(lean_object* v_x_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l_Lean_Meta_PProdN_reduceProjs___lam__0(v_x_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec_ref(v_x_1032_);
return v_res_1038_;
}
}
lean_object* l_Lean_Meta_PProdN_reduceProjs___lam__1(lean_object* v_e_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_){
_start:
{
lean_object* v_e_x27_1062_; lean_object* v_e_x27_1066_; lean_object* v___x_1076_; 
lean_inc_ref(v_e_1055_);
v___x_1076_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1055_, v___y_1057_);
if (lean_obj_tag(v___x_1076_) == 0)
{
lean_object* v_a_1077_; lean_object* v___x_1078_; uint8_t v___x_1079_; 
v_a_1077_ = lean_ctor_get(v___x_1076_, 0);
lean_inc(v_a_1077_);
lean_dec_ref_known(v___x_1076_, 1);
v___x_1078_ = l_Lean_Expr_cleanupAnnotations(v_a_1077_);
v___x_1079_ = l_Lean_Expr_isApp(v___x_1078_);
if (v___x_1079_ == 0)
{
lean_dec_ref(v___x_1078_);
goto v___jp_1069_;
}
else
{
lean_object* v_arg_1080_; lean_object* v___x_1081_; uint8_t v___x_1082_; 
v_arg_1080_ = lean_ctor_get(v___x_1078_, 1);
lean_inc_ref(v_arg_1080_);
v___x_1081_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1078_);
v___x_1082_ = l_Lean_Expr_isApp(v___x_1081_);
if (v___x_1082_ == 0)
{
lean_dec_ref(v___x_1081_);
lean_dec_ref(v_arg_1080_);
goto v___jp_1069_;
}
else
{
lean_object* v___x_1083_; uint8_t v___x_1084_; 
v___x_1083_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1081_);
v___x_1084_ = l_Lean_Expr_isApp(v___x_1083_);
if (v___x_1084_ == 0)
{
lean_dec_ref(v___x_1083_);
lean_dec_ref(v_arg_1080_);
goto v___jp_1069_;
}
else
{
lean_object* v___x_1085_; lean_object* v___x_1086_; uint8_t v___x_1087_; 
v___x_1085_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1083_);
v___x_1086_ = ((lean_object*)(l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__1));
v___x_1087_ = l_Lean_Expr_isConstOf(v___x_1085_, v___x_1086_);
if (v___x_1087_ == 0)
{
lean_object* v___x_1088_; uint8_t v___x_1089_; 
v___x_1088_ = ((lean_object*)(l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__3));
v___x_1089_ = l_Lean_Expr_isConstOf(v___x_1085_, v___x_1088_);
if (v___x_1089_ == 0)
{
lean_object* v___x_1090_; uint8_t v___x_1091_; 
v___x_1090_ = ((lean_object*)(l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__5));
v___x_1091_ = l_Lean_Expr_isConstOf(v___x_1085_, v___x_1090_);
if (v___x_1091_ == 0)
{
lean_object* v___x_1092_; uint8_t v___x_1093_; 
v___x_1092_ = ((lean_object*)(l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__7));
v___x_1093_ = l_Lean_Expr_isConstOf(v___x_1085_, v___x_1092_);
lean_dec_ref(v___x_1085_);
if (v___x_1093_ == 0)
{
lean_dec_ref(v_arg_1080_);
goto v___jp_1069_;
}
else
{
lean_dec_ref(v_e_1055_);
v_e_x27_1066_ = v_arg_1080_;
goto v___jp_1065_;
}
}
else
{
lean_dec_ref(v___x_1085_);
lean_dec_ref(v_e_1055_);
v_e_x27_1066_ = v_arg_1080_;
goto v___jp_1065_;
}
}
else
{
lean_dec_ref(v___x_1085_);
lean_dec_ref(v_e_1055_);
v_e_x27_1062_ = v_arg_1080_;
goto v___jp_1061_;
}
}
else
{
lean_dec_ref(v___x_1085_);
lean_dec_ref(v_e_1055_);
v_e_x27_1062_ = v_arg_1080_;
goto v___jp_1061_;
}
}
}
}
}
else
{
lean_object* v_a_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1101_; 
lean_dec_ref(v_e_1055_);
v_a_1094_ = lean_ctor_get(v___x_1076_, 0);
v_isSharedCheck_1101_ = !lean_is_exclusive(v___x_1076_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1096_ = v___x_1076_;
v_isShared_1097_ = v_isSharedCheck_1101_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_a_1094_);
lean_dec(v___x_1076_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1101_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v___x_1099_; 
if (v_isShared_1097_ == 0)
{
v___x_1099_ = v___x_1096_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v_a_1094_);
v___x_1099_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
return v___x_1099_;
}
}
}
v___jp_1061_:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1063_ = lean_unsigned_to_nat(1u);
v___x_1064_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___redArg(v_e_x27_1062_, v___x_1063_);
lean_dec_ref(v_e_x27_1062_);
return v___x_1064_;
}
v___jp_1065_:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1067_ = lean_unsigned_to_nat(0u);
v___x_1068_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___redArg(v_e_x27_1066_, v___x_1067_);
lean_dec_ref(v_e_x27_1066_);
return v___x_1068_;
}
v___jp_1069_:
{
uint8_t v___x_1070_; 
v___x_1070_ = l_Lean_Expr_isProj(v_e_1055_);
if (v___x_1070_ == 0)
{
lean_object* v___x_1071_; lean_object* v___x_1072_; 
lean_dec_ref(v_e_1055_);
v___x_1071_ = ((lean_object*)(l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___redArg___closed__0));
v___x_1072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1071_);
return v___x_1072_;
}
else
{
lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1073_ = l_Lean_Expr_projExpr_x21(v_e_1055_);
v___x_1074_ = l_Lean_Expr_projIdx_x21(v_e_1055_);
lean_dec_ref(v_e_1055_);
v___x_1075_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___redArg(v___x_1073_, v___x_1074_);
lean_dec(v___x_1074_);
lean_dec_ref(v___x_1073_);
return v___x_1075_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_PProdN_reduceProjs___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1055_ = stack[0].m_obj;
lean_object* v___y_1056_ = stack[1].m_obj;
lean_object* v___y_1057_ = stack[2].m_obj;
lean_object* v___y_1058_ = stack[3].m_obj;
lean_object* v___y_1059_ = stack[4].m_obj;
lean_object* v_res_1102_;
v_res_1102_ = l_Lean_Meta_PProdN_reduceProjs___lam__1(v_e_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_);
stack->m_obj
 = v_res_1102_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_reduceProjs___lam__1___boxed(lean_object* v_e_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_){
_start:
{
lean_object* v_res_1109_; 
v_res_1109_ = l_Lean_Meta_PProdN_reduceProjs___lam__1(v_e_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_);
lean_dec(v___y_1107_);
lean_dec_ref(v___y_1106_);
lean_dec(v___y_1105_);
lean_dec_ref(v___y_1104_);
return v_res_1109_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3_spec__4___redArg(lean_object* v_a_1110_, lean_object* v_x_1111_){
_start:
{
if (lean_obj_tag(v_x_1111_) == 0)
{
lean_object* v___x_1112_; 
v___x_1112_ = lean_box(0);
return v___x_1112_;
}
else
{
lean_object* v_key_1113_; lean_object* v_value_1114_; lean_object* v_tail_1115_; uint8_t v___x_1116_; 
v_key_1113_ = lean_ctor_get(v_x_1111_, 0);
v_value_1114_ = lean_ctor_get(v_x_1111_, 1);
v_tail_1115_ = lean_ctor_get(v_x_1111_, 2);
v___x_1116_ = l_Lean_ExprStructEq_beq(v_key_1113_, v_a_1110_);
if (v___x_1116_ == 0)
{
v_x_1111_ = v_tail_1115_;
goto _start;
}
else
{
lean_object* v___x_1118_; 
lean_inc(v_value_1114_);
v___x_1118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1118_, 0, v_value_1114_);
return v___x_1118_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object* v_a_1119_, lean_object* v_x_1120_){
_start:
{
lean_object* v_res_1121_; 
v_res_1121_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3_spec__4___redArg(v_a_1119_, v_x_1120_);
lean_dec(v_x_1120_);
lean_dec_ref(v_a_1119_);
return v_res_1121_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3___redArg(lean_object* v_m_1122_, lean_object* v_a_1123_){
_start:
{
lean_object* v_buckets_1124_; lean_object* v___x_1125_; uint64_t v___x_1126_; uint64_t v___x_1127_; uint64_t v___x_1128_; uint64_t v_fold_1129_; uint64_t v___x_1130_; uint64_t v___x_1131_; uint64_t v___x_1132_; size_t v___x_1133_; size_t v___x_1134_; size_t v___x_1135_; size_t v___x_1136_; size_t v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
v_buckets_1124_ = lean_ctor_get(v_m_1122_, 1);
v___x_1125_ = lean_array_get_size(v_buckets_1124_);
v___x_1126_ = l_Lean_ExprStructEq_hash(v_a_1123_);
v___x_1127_ = 32ULL;
v___x_1128_ = lean_uint64_shift_right(v___x_1126_, v___x_1127_);
v_fold_1129_ = lean_uint64_xor(v___x_1126_, v___x_1128_);
v___x_1130_ = 16ULL;
v___x_1131_ = lean_uint64_shift_right(v_fold_1129_, v___x_1130_);
v___x_1132_ = lean_uint64_xor(v_fold_1129_, v___x_1131_);
v___x_1133_ = lean_uint64_to_usize(v___x_1132_);
v___x_1134_ = lean_usize_of_nat(v___x_1125_);
v___x_1135_ = ((size_t)1ULL);
v___x_1136_ = lean_usize_sub(v___x_1134_, v___x_1135_);
v___x_1137_ = lean_usize_land(v___x_1133_, v___x_1136_);
v___x_1138_ = lean_array_uget_borrowed(v_buckets_1124_, v___x_1137_);
v___x_1139_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3_spec__4___redArg(v_a_1123_, v___x_1138_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_m_1140_, lean_object* v_a_1141_){
_start:
{
lean_object* v_res_1142_; 
v_res_1142_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3___redArg(v_m_1140_, v_a_1141_);
lean_dec_ref(v_a_1141_);
lean_dec_ref(v_m_1140_);
return v_res_1142_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__12___redArg(lean_object* v_a_1143_, lean_object* v_b_1144_, lean_object* v_x_1145_){
_start:
{
if (lean_obj_tag(v_x_1145_) == 0)
{
lean_dec(v_b_1144_);
lean_dec_ref(v_a_1143_);
return v_x_1145_;
}
else
{
lean_object* v_key_1146_; lean_object* v_value_1147_; lean_object* v_tail_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1160_; 
v_key_1146_ = lean_ctor_get(v_x_1145_, 0);
v_value_1147_ = lean_ctor_get(v_x_1145_, 1);
v_tail_1148_ = lean_ctor_get(v_x_1145_, 2);
v_isSharedCheck_1160_ = !lean_is_exclusive(v_x_1145_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1150_ = v_x_1145_;
v_isShared_1151_ = v_isSharedCheck_1160_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_tail_1148_);
lean_inc(v_value_1147_);
lean_inc(v_key_1146_);
lean_dec(v_x_1145_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1160_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
uint8_t v___x_1152_; 
v___x_1152_ = l_Lean_ExprStructEq_beq(v_key_1146_, v_a_1143_);
if (v___x_1152_ == 0)
{
lean_object* v___x_1153_; lean_object* v___x_1155_; 
v___x_1153_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__12___redArg(v_a_1143_, v_b_1144_, v_tail_1148_);
if (v_isShared_1151_ == 0)
{
lean_ctor_set(v___x_1150_, 2, v___x_1153_);
v___x_1155_ = v___x_1150_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_key_1146_);
lean_ctor_set(v_reuseFailAlloc_1156_, 1, v_value_1147_);
lean_ctor_set(v_reuseFailAlloc_1156_, 2, v___x_1153_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
else
{
lean_object* v___x_1158_; 
lean_dec(v_value_1147_);
lean_dec(v_key_1146_);
if (v_isShared_1151_ == 0)
{
lean_ctor_set(v___x_1150_, 1, v_b_1144_);
lean_ctor_set(v___x_1150_, 0, v_a_1143_);
v___x_1158_ = v___x_1150_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_a_1143_);
lean_ctor_set(v_reuseFailAlloc_1159_, 1, v_b_1144_);
lean_ctor_set(v_reuseFailAlloc_1159_, 2, v_tail_1148_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(lean_object* v_x_1161_, lean_object* v_x_1162_){
_start:
{
if (lean_obj_tag(v_x_1162_) == 0)
{
return v_x_1161_;
}
else
{
lean_object* v_key_1163_; lean_object* v_value_1164_; lean_object* v_tail_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1188_; 
v_key_1163_ = lean_ctor_get(v_x_1162_, 0);
v_value_1164_ = lean_ctor_get(v_x_1162_, 1);
v_tail_1165_ = lean_ctor_get(v_x_1162_, 2);
v_isSharedCheck_1188_ = !lean_is_exclusive(v_x_1162_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_1167_ = v_x_1162_;
v_isShared_1168_ = v_isSharedCheck_1188_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_tail_1165_);
lean_inc(v_value_1164_);
lean_inc(v_key_1163_);
lean_dec(v_x_1162_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1188_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v___x_1169_; uint64_t v___x_1170_; uint64_t v___x_1171_; uint64_t v___x_1172_; uint64_t v_fold_1173_; uint64_t v___x_1174_; uint64_t v___x_1175_; uint64_t v___x_1176_; size_t v___x_1177_; size_t v___x_1178_; size_t v___x_1179_; size_t v___x_1180_; size_t v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1184_; 
v___x_1169_ = lean_array_get_size(v_x_1161_);
v___x_1170_ = l_Lean_ExprStructEq_hash(v_key_1163_);
v___x_1171_ = 32ULL;
v___x_1172_ = lean_uint64_shift_right(v___x_1170_, v___x_1171_);
v_fold_1173_ = lean_uint64_xor(v___x_1170_, v___x_1172_);
v___x_1174_ = 16ULL;
v___x_1175_ = lean_uint64_shift_right(v_fold_1173_, v___x_1174_);
v___x_1176_ = lean_uint64_xor(v_fold_1173_, v___x_1175_);
v___x_1177_ = lean_uint64_to_usize(v___x_1176_);
v___x_1178_ = lean_usize_of_nat(v___x_1169_);
v___x_1179_ = ((size_t)1ULL);
v___x_1180_ = lean_usize_sub(v___x_1178_, v___x_1179_);
v___x_1181_ = lean_usize_land(v___x_1177_, v___x_1180_);
v___x_1182_ = lean_array_uget_borrowed(v_x_1161_, v___x_1181_);
lean_inc(v___x_1182_);
if (v_isShared_1168_ == 0)
{
lean_ctor_set(v___x_1167_, 2, v___x_1182_);
v___x_1184_ = v___x_1167_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v_key_1163_);
lean_ctor_set(v_reuseFailAlloc_1187_, 1, v_value_1164_);
lean_ctor_set(v_reuseFailAlloc_1187_, 2, v___x_1182_);
v___x_1184_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
lean_object* v___x_1185_; 
v___x_1185_ = lean_array_uset(v_x_1161_, v___x_1181_, v___x_1184_);
v_x_1161_ = v___x_1185_;
v_x_1162_ = v_tail_1165_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(lean_object* v_i_1189_, lean_object* v_source_1190_, lean_object* v_target_1191_){
_start:
{
lean_object* v___x_1192_; uint8_t v___x_1193_; 
v___x_1192_ = lean_array_get_size(v_source_1190_);
v___x_1193_ = lean_nat_dec_lt(v_i_1189_, v___x_1192_);
if (v___x_1193_ == 0)
{
lean_dec_ref(v_source_1190_);
lean_dec(v_i_1189_);
return v_target_1191_;
}
else
{
lean_object* v_es_1194_; lean_object* v___x_1195_; lean_object* v_source_1196_; lean_object* v_target_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; 
v_es_1194_ = lean_array_fget(v_source_1190_, v_i_1189_);
v___x_1195_ = lean_box(0);
v_source_1196_ = lean_array_fset(v_source_1190_, v_i_1189_, v___x_1195_);
v_target_1197_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_target_1191_, v_es_1194_);
v___x_1198_ = lean_unsigned_to_nat(1u);
v___x_1199_ = lean_nat_add(v_i_1189_, v___x_1198_);
lean_dec(v_i_1189_);
v_i_1189_ = v___x_1199_;
v_source_1190_ = v_source_1196_;
v_target_1191_ = v_target_1197_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11___redArg(lean_object* v_data_1201_){
_start:
{
lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v_nbuckets_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1202_ = lean_array_get_size(v_data_1201_);
v___x_1203_ = lean_unsigned_to_nat(2u);
v_nbuckets_1204_ = lean_nat_mul(v___x_1202_, v___x_1203_);
v___x_1205_ = lean_unsigned_to_nat(0u);
v___x_1206_ = lean_box(0);
v___x_1207_ = lean_mk_array(v_nbuckets_1204_, v___x_1206_);
v___x_1208_ = lean_array_propagate_mark(v_data_1201_, v___x_1207_);
v___x_1209_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v___x_1205_, v_data_1201_, v___x_1208_);
return v___x_1209_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__10___redArg(lean_object* v_a_1210_, lean_object* v_x_1211_){
_start:
{
if (lean_obj_tag(v_x_1211_) == 0)
{
uint8_t v___x_1212_; 
v___x_1212_ = 0;
return v___x_1212_;
}
else
{
lean_object* v_key_1213_; lean_object* v_tail_1214_; uint8_t v___x_1215_; 
v_key_1213_ = lean_ctor_get(v_x_1211_, 0);
v_tail_1214_ = lean_ctor_get(v_x_1211_, 2);
v___x_1215_ = l_Lean_ExprStructEq_beq(v_key_1213_, v_a_1210_);
if (v___x_1215_ == 0)
{
v_x_1211_ = v_tail_1214_;
goto _start;
}
else
{
return v___x_1215_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__10___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1210_ = stack[0].m_obj;
lean_object* v_x_1211_ = stack[1].m_obj;
uint8_t v_res_1217_;
v_res_1217_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__10___redArg(v_a_1210_, v_x_1211_);
stack->m_num = v_res_1217_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__10___redArg___boxed(lean_object* v_a_1218_, lean_object* v_x_1219_){
_start:
{
uint8_t v_res_1220_; lean_object* v_r_1221_; 
v_res_1220_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__10___redArg(v_a_1218_, v_x_1219_);
lean_dec(v_x_1219_);
lean_dec_ref(v_a_1218_);
v_r_1221_ = lean_box(v_res_1220_);
return v_r_1221_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6___redArg(lean_object* v_m_1222_, lean_object* v_a_1223_, lean_object* v_b_1224_){
_start:
{
lean_object* v_size_1225_; lean_object* v_buckets_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1269_; 
v_size_1225_ = lean_ctor_get(v_m_1222_, 0);
v_buckets_1226_ = lean_ctor_get(v_m_1222_, 1);
v_isSharedCheck_1269_ = !lean_is_exclusive(v_m_1222_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1228_ = v_m_1222_;
v_isShared_1229_ = v_isSharedCheck_1269_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_buckets_1226_);
lean_inc(v_size_1225_);
lean_dec(v_m_1222_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1269_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1230_; uint64_t v___x_1231_; uint64_t v___x_1232_; uint64_t v___x_1233_; uint64_t v_fold_1234_; uint64_t v___x_1235_; uint64_t v___x_1236_; uint64_t v___x_1237_; size_t v___x_1238_; size_t v___x_1239_; size_t v___x_1240_; size_t v___x_1241_; size_t v___x_1242_; lean_object* v_bkt_1243_; uint8_t v___x_1244_; 
v___x_1230_ = lean_array_get_size(v_buckets_1226_);
v___x_1231_ = l_Lean_ExprStructEq_hash(v_a_1223_);
v___x_1232_ = 32ULL;
v___x_1233_ = lean_uint64_shift_right(v___x_1231_, v___x_1232_);
v_fold_1234_ = lean_uint64_xor(v___x_1231_, v___x_1233_);
v___x_1235_ = 16ULL;
v___x_1236_ = lean_uint64_shift_right(v_fold_1234_, v___x_1235_);
v___x_1237_ = lean_uint64_xor(v_fold_1234_, v___x_1236_);
v___x_1238_ = lean_uint64_to_usize(v___x_1237_);
v___x_1239_ = lean_usize_of_nat(v___x_1230_);
v___x_1240_ = ((size_t)1ULL);
v___x_1241_ = lean_usize_sub(v___x_1239_, v___x_1240_);
v___x_1242_ = lean_usize_land(v___x_1238_, v___x_1241_);
v_bkt_1243_ = lean_array_uget_borrowed(v_buckets_1226_, v___x_1242_);
v___x_1244_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__10___redArg(v_a_1223_, v_bkt_1243_);
if (v___x_1244_ == 0)
{
lean_object* v___x_1245_; lean_object* v_size_x27_1246_; lean_object* v___x_1247_; lean_object* v_buckets_x27_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; uint8_t v___x_1254_; 
v___x_1245_ = lean_unsigned_to_nat(1u);
v_size_x27_1246_ = lean_nat_add(v_size_1225_, v___x_1245_);
lean_dec(v_size_1225_);
lean_inc(v_bkt_1243_);
v___x_1247_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1247_, 0, v_a_1223_);
lean_ctor_set(v___x_1247_, 1, v_b_1224_);
lean_ctor_set(v___x_1247_, 2, v_bkt_1243_);
v_buckets_x27_1248_ = lean_array_uset(v_buckets_1226_, v___x_1242_, v___x_1247_);
v___x_1249_ = lean_unsigned_to_nat(4u);
v___x_1250_ = lean_nat_mul(v_size_x27_1246_, v___x_1249_);
v___x_1251_ = lean_unsigned_to_nat(3u);
v___x_1252_ = lean_nat_div(v___x_1250_, v___x_1251_);
lean_dec(v___x_1250_);
v___x_1253_ = lean_array_get_size(v_buckets_x27_1248_);
v___x_1254_ = lean_nat_dec_le(v___x_1252_, v___x_1253_);
lean_dec(v___x_1252_);
if (v___x_1254_ == 0)
{
lean_object* v_val_1255_; lean_object* v___x_1257_; 
v_val_1255_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11___redArg(v_buckets_x27_1248_);
if (v_isShared_1229_ == 0)
{
lean_ctor_set(v___x_1228_, 1, v_val_1255_);
lean_ctor_set(v___x_1228_, 0, v_size_x27_1246_);
v___x_1257_ = v___x_1228_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v_size_x27_1246_);
lean_ctor_set(v_reuseFailAlloc_1258_, 1, v_val_1255_);
v___x_1257_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
return v___x_1257_;
}
}
else
{
lean_object* v___x_1260_; 
if (v_isShared_1229_ == 0)
{
lean_ctor_set(v___x_1228_, 1, v_buckets_x27_1248_);
lean_ctor_set(v___x_1228_, 0, v_size_x27_1246_);
v___x_1260_ = v___x_1228_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v_size_x27_1246_);
lean_ctor_set(v_reuseFailAlloc_1261_, 1, v_buckets_x27_1248_);
v___x_1260_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
return v___x_1260_;
}
}
}
else
{
lean_object* v___x_1262_; lean_object* v_buckets_x27_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1267_; 
lean_inc(v_bkt_1243_);
v___x_1262_ = lean_box(0);
v_buckets_x27_1263_ = lean_array_uset(v_buckets_1226_, v___x_1242_, v___x_1262_);
v___x_1264_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__12___redArg(v_a_1223_, v_b_1224_, v_bkt_1243_);
v___x_1265_ = lean_array_uset(v_buckets_x27_1263_, v___x_1242_, v___x_1264_);
if (v_isShared_1229_ == 0)
{
lean_ctor_set(v___x_1228_, 1, v___x_1265_);
v___x_1267_ = v___x_1228_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_size_1225_);
lean_ctor_set(v_reuseFailAlloc_1268_, 1, v___x_1265_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
return v___x_1267_;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__2(lean_object* v_a_1270_, lean_object* v_e_1271_, lean_object* v_a_1272_){
_start:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; 
v___x_1274_ = lean_st_ref_take(v_a_1270_);
v___x_1275_ = lean_box(0);
v___x_1276_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6___redArg(v___x_1274_, v_e_1271_, v_a_1272_);
v___x_1277_ = lean_st_ref_put(v_a_1270_, v___x_1276_);
return v___x_1275_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1270_ = stack[0].m_obj;
lean_object* v_e_1271_ = stack[1].m_obj;
lean_object* v_a_1272_ = stack[2].m_obj;
lean_object* v_res_1278_;
v_res_1278_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__2(v_a_1270_, v_e_1271_, v_a_1272_);
stack->m_obj
 = v_res_1278_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__2___boxed(lean_object* v_a_1279_, lean_object* v_e_1280_, lean_object* v_a_1281_, lean_object* v___y_1282_){
_start:
{
lean_object* v_res_1283_; 
v_res_1283_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__2(v_a_1279_, v_e_1280_, v_a_1281_);
lean_dec(v_a_1279_);
return v_res_1283_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_1284_, lean_object* v_x_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_){
_start:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1291_ = lean_apply_1(v_x_1285_, lean_box(0));
v___x_1292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1292_, 0, v___x_1291_);
return v___x_1292_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1285_ = stack[1].m_obj;
lean_object* v___y_1286_ = stack[2].m_obj;
lean_object* v___y_1287_ = stack[3].m_obj;
lean_object* v___y_1288_ = stack[4].m_obj;
lean_object* v___y_1289_ = stack[5].m_obj;
lean_object* v_res_1293_;
v_res_1293_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__0(lean_box(0), v_x_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_);
stack->m_obj
 = v_res_1293_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_1294_, lean_object* v_x_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_){
_start:
{
lean_object* v_res_1301_; 
v_res_1301_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__0(v_00_u03b1_1294_, v_x_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_);
lean_dec(v___y_1299_);
lean_dec_ref(v___y_1298_);
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1296_);
return v_res_1301_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; 
v___x_1302_ = lean_box(0);
v___x_1303_ = l_Lean_interruptExceptionId;
v___x_1304_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1304_, 0, v___x_1303_);
lean_ctor_set(v___x_1304_, 1, v___x_1302_);
return v___x_1304_;
}
}
lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__8___redArg(){
_start:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1306_ = lean_obj_once(&l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__8___redArg___closed__0, &l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__8___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__8___redArg___closed__0);
v___x_1307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1307_, 0, v___x_1306_);
return v___x_1307_;
}
}
LEAN_EXPORT void l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1308_;
v_res_1308_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__8___redArg();
stack->m_obj
 = v_res_1308_;
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__8___redArg___boxed(lean_object* v___y_1309_){
_start:
{
lean_object* v_res_1310_; 
v_res_1310_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__8___redArg();
return v_res_1310_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1316_ = l_Lean_maxRecDepthErrorMessage;
v___x_1317_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1316_);
return v___x_1317_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1318_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__3);
v___x_1319_ = l_Lean_MessageData_ofFormat(v___x_1318_);
return v___x_1319_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; 
v___x_1320_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__4);
v___x_1321_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__2));
v___x_1322_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1322_, 0, v___x_1321_);
lean_ctor_set(v___x_1322_, 1, v___x_1320_);
return v___x_1322_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg(lean_object* v_ref_1323_){
_start:
{
lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; 
v___x_1325_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__5);
v___x_1326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1326_, 0, v_ref_1323_);
lean_ctor_set(v___x_1326_, 1, v___x_1325_);
v___x_1327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1327_, 0, v___x_1326_);
return v___x_1327_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1323_ = stack[0].m_obj;
lean_object* v_res_1328_;
v_res_1328_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_1323_);
stack->m_obj
 = v_res_1328_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object* v_ref_1329_, lean_object* v___y_1330_){
_start:
{
lean_object* v_res_1331_; 
v_res_1331_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_1329_);
return v_res_1331_;
}
}
lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5___redArg(lean_object* v_x_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_){
_start:
{
lean_object* v___y_1340_; uint8_t v___y_1350_; lean_object* v___y_1351_; lean_object* v___y_1352_; lean_object* v___y_1353_; uint8_t v___y_1354_; uint16_t v___y_1355_; lean_object* v_toCold_1360_; lean_object* v_currRecDepth_1361_; lean_object* v_ref_1362_; uint16_t v_optionFlags_1363_; uint8_t v_suppressElabErrors_1364_; uint8_t v_isRecordingDeps_1365_; lean_object* v_maxRecDepth_1366_; lean_object* v_cancelTk_x3f_1367_; 
v_toCold_1360_ = lean_ctor_get(v___y_1336_, 0);
v_currRecDepth_1361_ = lean_ctor_get(v___y_1336_, 1);
v_ref_1362_ = lean_ctor_get(v___y_1336_, 2);
v_optionFlags_1363_ = lean_ctor_get_uint16(v___y_1336_, sizeof(void*)*3);
v_suppressElabErrors_1364_ = lean_ctor_get_uint8(v___y_1336_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1365_ = lean_ctor_get_uint8(v___y_1336_, sizeof(void*)*3 + 3);
v_maxRecDepth_1366_ = lean_ctor_get(v_toCold_1360_, 3);
v_cancelTk_x3f_1367_ = lean_ctor_get(v_toCold_1360_, 10);
if (lean_obj_tag(v_cancelTk_x3f_1367_) == 1)
{
lean_object* v_val_1373_; uint8_t v___x_1374_; 
v_val_1373_ = lean_ctor_get(v_cancelTk_x3f_1367_, 0);
v___x_1374_ = l_IO_CancelToken_isSet(v_val_1373_);
if (v___x_1374_ == 0)
{
goto v___jp_1368_;
}
else
{
lean_object* v___x_1375_; lean_object* v_a_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1383_; 
lean_dec_ref(v_x_1332_);
v___x_1375_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__8___redArg();
v_a_1376_ = lean_ctor_get(v___x_1375_, 0);
v_isSharedCheck_1383_ = !lean_is_exclusive(v___x_1375_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1378_ = v___x_1375_;
v_isShared_1379_ = v_isSharedCheck_1383_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_a_1376_);
lean_dec(v___x_1375_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1383_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
lean_object* v___x_1381_; 
if (v_isShared_1379_ == 0)
{
v___x_1381_ = v___x_1378_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v_a_1376_);
v___x_1381_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
return v___x_1381_;
}
}
}
}
else
{
goto v___jp_1368_;
}
v___jp_1339_:
{
if (lean_obj_tag(v___y_1340_) == 0)
{
return v___y_1340_;
}
else
{
lean_object* v_a_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1348_; 
v_a_1341_ = lean_ctor_get(v___y_1340_, 0);
v_isSharedCheck_1348_ = !lean_is_exclusive(v___y_1340_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1343_ = v___y_1340_;
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_a_1341_);
lean_dec(v___y_1340_);
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
v___jp_1349_:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___x_1356_ = lean_unsigned_to_nat(1u);
v___x_1357_ = lean_nat_add(v___y_1353_, v___x_1356_);
lean_inc_ref(v___y_1352_);
v___x_1358_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1358_, 0, v___y_1352_);
lean_ctor_set(v___x_1358_, 1, v___x_1357_);
lean_ctor_set(v___x_1358_, 2, v___y_1351_);
lean_ctor_set_uint16(v___x_1358_, sizeof(void*)*3, v___y_1355_);
lean_ctor_set_uint8(v___x_1358_, sizeof(void*)*3 + 2, v___y_1350_);
lean_ctor_set_uint8(v___x_1358_, sizeof(void*)*3 + 3, v___y_1354_);
lean_inc(v___y_1337_);
lean_inc(v___y_1335_);
lean_inc_ref(v___y_1334_);
lean_inc(v___y_1333_);
v___x_1359_ = lean_apply_6(v_x_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___x_1358_, v___y_1337_, lean_box(0));
v___y_1340_ = v___x_1359_;
goto v___jp_1339_;
}
v___jp_1368_:
{
lean_object* v___x_1369_; uint8_t v___x_1370_; 
v___x_1369_ = lean_unsigned_to_nat(0u);
v___x_1370_ = lean_nat_dec_eq(v_maxRecDepth_1366_, v___x_1369_);
if (v___x_1370_ == 0)
{
uint8_t v___x_1371_; 
v___x_1371_ = lean_nat_dec_eq(v_currRecDepth_1361_, v_maxRecDepth_1366_);
if (v___x_1371_ == 0)
{
lean_inc(v_ref_1362_);
v___y_1350_ = v_suppressElabErrors_1364_;
v___y_1351_ = v_ref_1362_;
v___y_1352_ = v_toCold_1360_;
v___y_1353_ = v_currRecDepth_1361_;
v___y_1354_ = v_isRecordingDeps_1365_;
v___y_1355_ = v_optionFlags_1363_;
goto v___jp_1349_;
}
else
{
lean_object* v___x_1372_; 
lean_dec_ref(v_x_1332_);
lean_inc(v_ref_1362_);
v___x_1372_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_1362_);
v___y_1340_ = v___x_1372_;
goto v___jp_1339_;
}
}
else
{
lean_inc(v_ref_1362_);
v___y_1350_ = v_suppressElabErrors_1364_;
v___y_1351_ = v_ref_1362_;
v___y_1352_ = v_toCold_1360_;
v___y_1353_ = v_currRecDepth_1361_;
v___y_1354_ = v_isRecordingDeps_1365_;
v___y_1355_ = v_optionFlags_1363_;
goto v___jp_1349_;
}
}
}
}
LEAN_EXPORT void l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1332_ = stack[0].m_obj;
lean_object* v___y_1333_ = stack[1].m_obj;
lean_object* v___y_1334_ = stack[2].m_obj;
lean_object* v___y_1335_ = stack[3].m_obj;
lean_object* v___y_1336_ = stack[4].m_obj;
lean_object* v___y_1337_ = stack[5].m_obj;
lean_object* v_res_1384_;
v_res_1384_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5___redArg(v_x_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_);
stack->m_obj
 = v_res_1384_;
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_x_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_){
_start:
{
lean_object* v_res_1392_; 
v_res_1392_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5___redArg(v_x_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_);
lean_dec(v___y_1390_);
lean_dec_ref(v___y_1389_);
lean_dec(v___y_1388_);
lean_dec_ref(v___y_1387_);
lean_dec(v___y_1386_);
return v_res_1392_;
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__1___closed__0(void){
_start:
{
lean_object* v___x_1394_; lean_object* v_dummy_1395_; 
v___x_1394_ = lean_box(0);
v_dummy_1395_ = l_Lean_Expr_sort___override(v___x_1394_);
return v_dummy_1395_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__1(lean_object* v_pre_1396_, lean_object* v_post_1397_, size_t v_sz_1398_, size_t v_i_1399_, lean_object* v_bs_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_){
_start:
{
uint8_t v___x_1407_; 
v___x_1407_ = lean_usize_dec_lt(v_i_1399_, v_sz_1398_);
if (v___x_1407_ == 0)
{
lean_object* v___x_1408_; 
lean_dec_ref(v_post_1397_);
lean_dec_ref(v_pre_1396_);
v___x_1408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1408_, 0, v_bs_1400_);
return v___x_1408_;
}
else
{
lean_object* v_v_1409_; lean_object* v___x_1410_; lean_object* v_bs_x27_1411_; lean_object* v___x_1412_; 
v_v_1409_ = lean_array_uget(v_bs_1400_, v_i_1399_);
v___x_1410_ = lean_unsigned_to_nat(0u);
v_bs_x27_1411_ = lean_array_uset(v_bs_1400_, v_i_1399_, v___x_1410_);
lean_inc_ref(v_post_1397_);
lean_inc_ref(v_pre_1396_);
v___x_1412_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1396_, v_post_1397_, v_v_1409_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_);
if (lean_obj_tag(v___x_1412_) == 0)
{
lean_object* v_a_1413_; size_t v___x_1414_; size_t v___x_1415_; lean_object* v___x_1416_; 
v_a_1413_ = lean_ctor_get(v___x_1412_, 0);
lean_inc(v_a_1413_);
lean_dec_ref_known(v___x_1412_, 1);
v___x_1414_ = ((size_t)1ULL);
v___x_1415_ = lean_usize_add(v_i_1399_, v___x_1414_);
v___x_1416_ = lean_array_uset(v_bs_x27_1411_, v_i_1399_, v_a_1413_);
v_i_1399_ = v___x_1415_;
v_bs_1400_ = v___x_1416_;
goto _start;
}
else
{
lean_object* v_a_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1425_; 
lean_dec_ref(v_bs_x27_1411_);
lean_dec_ref(v_post_1397_);
lean_dec_ref(v_pre_1396_);
v_a_1418_ = lean_ctor_get(v___x_1412_, 0);
v_isSharedCheck_1425_ = !lean_is_exclusive(v___x_1412_);
if (v_isSharedCheck_1425_ == 0)
{
v___x_1420_ = v___x_1412_;
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_a_1418_);
lean_dec(v___x_1412_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v___x_1423_; 
if (v_isShared_1421_ == 0)
{
v___x_1423_ = v___x_1420_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v_a_1418_);
v___x_1423_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
return v___x_1423_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_1396_ = stack[0].m_obj;
lean_object* v_post_1397_ = stack[1].m_obj;
size_t v_sz_1398_ = stack[2].m_num;
size_t v_i_1399_ = stack[3].m_num;
lean_object* v_bs_1400_ = stack[4].m_obj;
lean_object* v___y_1401_ = stack[5].m_obj;
lean_object* v___y_1402_ = stack[6].m_obj;
lean_object* v___y_1403_ = stack[7].m_obj;
lean_object* v___y_1404_ = stack[8].m_obj;
lean_object* v___y_1405_ = stack[9].m_obj;
lean_object* v_res_1426_;
v_res_1426_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__1(v_pre_1396_, v_post_1397_, v_sz_1398_, v_i_1399_, v_bs_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_);
stack->m_obj
 = v_res_1426_;
}
lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__4(lean_object* v_pre_1427_, lean_object* v_post_1428_, lean_object* v_x_1429_, lean_object* v_x_1430_, lean_object* v_x_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_){
_start:
{
if (lean_obj_tag(v_x_1429_) == 5)
{
lean_object* v_fn_1438_; lean_object* v_arg_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; 
v_fn_1438_ = lean_ctor_get(v_x_1429_, 0);
lean_inc_ref(v_fn_1438_);
v_arg_1439_ = lean_ctor_get(v_x_1429_, 1);
lean_inc_ref(v_arg_1439_);
lean_dec_ref_known(v_x_1429_, 2);
v___x_1440_ = lean_array_set(v_x_1430_, v_x_1431_, v_arg_1439_);
v___x_1441_ = lean_unsigned_to_nat(1u);
v___x_1442_ = lean_nat_sub(v_x_1431_, v___x_1441_);
lean_dec(v_x_1431_);
v_x_1429_ = v_fn_1438_;
v_x_1430_ = v___x_1440_;
v_x_1431_ = v___x_1442_;
goto _start;
}
else
{
lean_object* v___x_1444_; 
lean_dec(v_x_1431_);
lean_inc_ref(v_post_1428_);
lean_inc_ref(v_pre_1427_);
v___x_1444_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1427_, v_post_1428_, v_x_1429_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_);
if (lean_obj_tag(v___x_1444_) == 0)
{
lean_object* v_a_1445_; size_t v_sz_1446_; size_t v___x_1447_; lean_object* v___x_1448_; 
v_a_1445_ = lean_ctor_get(v___x_1444_, 0);
lean_inc(v_a_1445_);
lean_dec_ref_known(v___x_1444_, 1);
v_sz_1446_ = lean_array_size(v_x_1430_);
v___x_1447_ = ((size_t)0ULL);
lean_inc_ref(v_post_1428_);
lean_inc_ref(v_pre_1427_);
v___x_1448_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__1(v_pre_1427_, v_post_1428_, v_sz_1446_, v___x_1447_, v_x_1430_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_);
if (lean_obj_tag(v___x_1448_) == 0)
{
lean_object* v_a_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; 
v_a_1449_ = lean_ctor_get(v___x_1448_, 0);
lean_inc(v_a_1449_);
lean_dec_ref_known(v___x_1448_, 1);
v___x_1450_ = l_Lean_mkAppN(v_a_1445_, v_a_1449_);
lean_dec(v_a_1449_);
v___x_1451_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1427_, v_post_1428_, v___x_1450_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_);
return v___x_1451_;
}
else
{
lean_object* v_a_1452_; lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1459_; 
lean_dec(v_a_1445_);
lean_dec_ref(v_post_1428_);
lean_dec_ref(v_pre_1427_);
v_a_1452_ = lean_ctor_get(v___x_1448_, 0);
v_isSharedCheck_1459_ = !lean_is_exclusive(v___x_1448_);
if (v_isSharedCheck_1459_ == 0)
{
v___x_1454_ = v___x_1448_;
v_isShared_1455_ = v_isSharedCheck_1459_;
goto v_resetjp_1453_;
}
else
{
lean_inc(v_a_1452_);
lean_dec(v___x_1448_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1459_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
lean_object* v___x_1457_; 
if (v_isShared_1455_ == 0)
{
v___x_1457_ = v___x_1454_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v_a_1452_);
v___x_1457_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
return v___x_1457_;
}
}
}
}
else
{
lean_dec_ref(v_x_1430_);
lean_dec_ref(v_post_1428_);
lean_dec_ref(v_pre_1427_);
return v___x_1444_;
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_1427_ = stack[0].m_obj;
lean_object* v_post_1428_ = stack[1].m_obj;
lean_object* v_x_1429_ = stack[2].m_obj;
lean_object* v_x_1430_ = stack[3].m_obj;
lean_object* v_x_1431_ = stack[4].m_obj;
lean_object* v___y_1432_ = stack[5].m_obj;
lean_object* v___y_1433_ = stack[6].m_obj;
lean_object* v___y_1434_ = stack[7].m_obj;
lean_object* v___y_1435_ = stack[8].m_obj;
lean_object* v___y_1436_ = stack[9].m_obj;
lean_object* v_res_1460_;
v_res_1460_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__4(v_pre_1427_, v_post_1428_, v_x_1429_, v_x_1430_, v_x_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_);
stack->m_obj
 = v_res_1460_;
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__1(lean_object* v___x_1461_, lean_object* v_pre_1462_, lean_object* v_e_1463_, lean_object* v_post_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_){
_start:
{
lean_object* v___x_1471_; 
v___x_1471_ = l_Lean_Core_checkSystem(v___x_1461_, v___y_1468_, v___y_1469_);
if (lean_obj_tag(v___x_1471_) == 0)
{
lean_object* v___x_1472_; 
lean_dec_ref_known(v___x_1471_, 1);
lean_inc_ref(v_pre_1462_);
lean_inc(v___y_1469_);
lean_inc_ref(v___y_1468_);
lean_inc(v___y_1467_);
lean_inc_ref(v___y_1466_);
lean_inc_ref(v_e_1463_);
v___x_1472_ = lean_apply_6(v_pre_1462_, v_e_1463_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_, lean_box(0));
if (lean_obj_tag(v___x_1472_) == 0)
{
lean_object* v_a_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1588_; 
v_a_1473_ = lean_ctor_get(v___x_1472_, 0);
v_isSharedCheck_1588_ = !lean_is_exclusive(v___x_1472_);
if (v_isSharedCheck_1588_ == 0)
{
v___x_1475_ = v___x_1472_;
v_isShared_1476_ = v_isSharedCheck_1588_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_a_1473_);
lean_dec(v___x_1472_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1588_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___y_1478_; 
switch(lean_obj_tag(v_a_1473_))
{
case 0:
{
lean_object* v_e_1578_; lean_object* v___x_1580_; 
lean_dec_ref(v_post_1464_);
lean_dec_ref(v_e_1463_);
lean_dec_ref(v_pre_1462_);
v_e_1578_ = lean_ctor_get(v_a_1473_, 0);
lean_inc_ref(v_e_1578_);
lean_dec_ref_known(v_a_1473_, 1);
if (v_isShared_1476_ == 0)
{
lean_ctor_set(v___x_1475_, 0, v_e_1578_);
v___x_1580_ = v___x_1475_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v_e_1578_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
return v___x_1580_;
}
}
case 1:
{
lean_object* v_e_1582_; lean_object* v___x_1583_; 
lean_del_object(v___x_1475_);
lean_dec_ref(v_e_1463_);
v_e_1582_ = lean_ctor_get(v_a_1473_, 0);
lean_inc_ref(v_e_1582_);
lean_dec_ref_known(v_a_1473_, 1);
lean_inc_ref(v_post_1464_);
lean_inc_ref(v_pre_1462_);
v___x_1583_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1462_, v_post_1464_, v_e_1582_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
if (lean_obj_tag(v___x_1583_) == 0)
{
lean_object* v_a_1584_; lean_object* v___x_1585_; 
v_a_1584_ = lean_ctor_get(v___x_1583_, 0);
lean_inc(v_a_1584_);
lean_dec_ref_known(v___x_1583_, 1);
v___x_1585_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1462_, v_post_1464_, v_a_1584_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
return v___x_1585_;
}
else
{
lean_dec_ref(v_post_1464_);
lean_dec_ref(v_pre_1462_);
return v___x_1583_;
}
}
default: 
{
lean_object* v_e_x3f_1586_; 
lean_del_object(v___x_1475_);
v_e_x3f_1586_ = lean_ctor_get(v_a_1473_, 0);
lean_inc(v_e_x3f_1586_);
lean_dec_ref_known(v_a_1473_, 1);
if (lean_obj_tag(v_e_x3f_1586_) == 0)
{
v___y_1478_ = v_e_1463_;
goto v___jp_1477_;
}
else
{
lean_object* v_val_1587_; 
lean_dec_ref(v_e_1463_);
v_val_1587_ = lean_ctor_get(v_e_x3f_1586_, 0);
lean_inc(v_val_1587_);
lean_dec_ref_known(v_e_x3f_1586_, 1);
v___y_1478_ = v_val_1587_;
goto v___jp_1477_;
}
}
}
v___jp_1477_:
{
switch(lean_obj_tag(v___y_1478_))
{
case 7:
{
lean_object* v_binderName_1479_; lean_object* v_binderType_1480_; lean_object* v_body_1481_; uint8_t v_binderInfo_1482_; lean_object* v___x_1483_; 
v_binderName_1479_ = lean_ctor_get(v___y_1478_, 0);
v_binderType_1480_ = lean_ctor_get(v___y_1478_, 1);
v_body_1481_ = lean_ctor_get(v___y_1478_, 2);
v_binderInfo_1482_ = lean_ctor_get_uint8(v___y_1478_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1480_);
lean_inc_ref(v_post_1464_);
lean_inc_ref(v_pre_1462_);
v___x_1483_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1462_, v_post_1464_, v_binderType_1480_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
if (lean_obj_tag(v___x_1483_) == 0)
{
lean_object* v_a_1484_; lean_object* v___x_1485_; 
v_a_1484_ = lean_ctor_get(v___x_1483_, 0);
lean_inc(v_a_1484_);
lean_dec_ref_known(v___x_1483_, 1);
lean_inc_ref(v_body_1481_);
lean_inc_ref(v_post_1464_);
lean_inc_ref(v_pre_1462_);
v___x_1485_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1462_, v_post_1464_, v_body_1481_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
if (lean_obj_tag(v___x_1485_) == 0)
{
lean_object* v_a_1486_; size_t v___x_1487_; size_t v___x_1488_; uint8_t v___x_1489_; 
v_a_1486_ = lean_ctor_get(v___x_1485_, 0);
lean_inc(v_a_1486_);
lean_dec_ref_known(v___x_1485_, 1);
v___x_1487_ = lean_ptr_addr(v_binderType_1480_);
v___x_1488_ = lean_ptr_addr(v_a_1484_);
v___x_1489_ = lean_usize_dec_eq(v___x_1487_, v___x_1488_);
if (v___x_1489_ == 0)
{
lean_object* v___x_1490_; lean_object* v___x_1491_; 
lean_inc(v_binderName_1479_);
lean_dec_ref_known(v___y_1478_, 3);
v___x_1490_ = l_Lean_Expr_forallE___override(v_binderName_1479_, v_a_1484_, v_a_1486_, v_binderInfo_1482_);
v___x_1491_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1462_, v_post_1464_, v___x_1490_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
return v___x_1491_;
}
else
{
size_t v___x_1492_; size_t v___x_1493_; uint8_t v___x_1494_; 
v___x_1492_ = lean_ptr_addr(v_body_1481_);
v___x_1493_ = lean_ptr_addr(v_a_1486_);
v___x_1494_ = lean_usize_dec_eq(v___x_1492_, v___x_1493_);
if (v___x_1494_ == 0)
{
lean_object* v___x_1495_; lean_object* v___x_1496_; 
lean_inc(v_binderName_1479_);
lean_dec_ref_known(v___y_1478_, 3);
v___x_1495_ = l_Lean_Expr_forallE___override(v_binderName_1479_, v_a_1484_, v_a_1486_, v_binderInfo_1482_);
v___x_1496_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1462_, v_post_1464_, v___x_1495_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
return v___x_1496_;
}
else
{
uint8_t v___x_1497_; 
v___x_1497_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1482_, v_binderInfo_1482_);
if (v___x_1497_ == 0)
{
lean_object* v___x_1498_; lean_object* v___x_1499_; 
lean_inc(v_binderName_1479_);
lean_dec_ref_known(v___y_1478_, 3);
v___x_1498_ = l_Lean_Expr_forallE___override(v_binderName_1479_, v_a_1484_, v_a_1486_, v_binderInfo_1482_);
v___x_1499_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1462_, v_post_1464_, v___x_1498_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
return v___x_1499_;
}
else
{
lean_object* v___x_1500_; 
lean_dec(v_a_1486_);
lean_dec(v_a_1484_);
v___x_1500_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1462_, v_post_1464_, v___y_1478_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
return v___x_1500_;
}
}
}
}
else
{
lean_dec(v_a_1484_);
lean_dec_ref_known(v___y_1478_, 3);
lean_dec_ref(v_post_1464_);
lean_dec_ref(v_pre_1462_);
return v___x_1485_;
}
}
else
{
lean_dec_ref_known(v___y_1478_, 3);
lean_dec_ref(v_post_1464_);
lean_dec_ref(v_pre_1462_);
return v___x_1483_;
}
}
case 6:
{
lean_object* v_binderName_1501_; lean_object* v_binderType_1502_; lean_object* v_body_1503_; uint8_t v_binderInfo_1504_; lean_object* v___x_1505_; 
v_binderName_1501_ = lean_ctor_get(v___y_1478_, 0);
v_binderType_1502_ = lean_ctor_get(v___y_1478_, 1);
v_body_1503_ = lean_ctor_get(v___y_1478_, 2);
v_binderInfo_1504_ = lean_ctor_get_uint8(v___y_1478_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1502_);
lean_inc_ref(v_post_1464_);
lean_inc_ref(v_pre_1462_);
v___x_1505_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1462_, v_post_1464_, v_binderType_1502_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
if (lean_obj_tag(v___x_1505_) == 0)
{
lean_object* v_a_1506_; lean_object* v___x_1507_; 
v_a_1506_ = lean_ctor_get(v___x_1505_, 0);
lean_inc(v_a_1506_);
lean_dec_ref_known(v___x_1505_, 1);
lean_inc_ref(v_body_1503_);
lean_inc_ref(v_post_1464_);
lean_inc_ref(v_pre_1462_);
v___x_1507_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1462_, v_post_1464_, v_body_1503_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
if (lean_obj_tag(v___x_1507_) == 0)
{
lean_object* v_a_1508_; size_t v___x_1509_; size_t v___x_1510_; uint8_t v___x_1511_; 
v_a_1508_ = lean_ctor_get(v___x_1507_, 0);
lean_inc(v_a_1508_);
lean_dec_ref_known(v___x_1507_, 1);
v___x_1509_ = lean_ptr_addr(v_binderType_1502_);
v___x_1510_ = lean_ptr_addr(v_a_1506_);
v___x_1511_ = lean_usize_dec_eq(v___x_1509_, v___x_1510_);
if (v___x_1511_ == 0)
{
lean_object* v___x_1512_; lean_object* v___x_1513_; 
lean_inc(v_binderName_1501_);
lean_dec_ref_known(v___y_1478_, 3);
v___x_1512_ = l_Lean_Expr_lam___override(v_binderName_1501_, v_a_1506_, v_a_1508_, v_binderInfo_1504_);
v___x_1513_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1462_, v_post_1464_, v___x_1512_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
return v___x_1513_;
}
else
{
size_t v___x_1514_; size_t v___x_1515_; uint8_t v___x_1516_; 
v___x_1514_ = lean_ptr_addr(v_body_1503_);
v___x_1515_ = lean_ptr_addr(v_a_1508_);
v___x_1516_ = lean_usize_dec_eq(v___x_1514_, v___x_1515_);
if (v___x_1516_ == 0)
{
lean_object* v___x_1517_; lean_object* v___x_1518_; 
lean_inc(v_binderName_1501_);
lean_dec_ref_known(v___y_1478_, 3);
v___x_1517_ = l_Lean_Expr_lam___override(v_binderName_1501_, v_a_1506_, v_a_1508_, v_binderInfo_1504_);
v___x_1518_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1462_, v_post_1464_, v___x_1517_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
return v___x_1518_;
}
else
{
uint8_t v___x_1519_; 
v___x_1519_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1504_, v_binderInfo_1504_);
if (v___x_1519_ == 0)
{
lean_object* v___x_1520_; lean_object* v___x_1521_; 
lean_inc(v_binderName_1501_);
lean_dec_ref_known(v___y_1478_, 3);
v___x_1520_ = l_Lean_Expr_lam___override(v_binderName_1501_, v_a_1506_, v_a_1508_, v_binderInfo_1504_);
v___x_1521_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1462_, v_post_1464_, v___x_1520_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
return v___x_1521_;
}
else
{
lean_object* v___x_1522_; 
lean_dec(v_a_1508_);
lean_dec(v_a_1506_);
v___x_1522_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1462_, v_post_1464_, v___y_1478_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
return v___x_1522_;
}
}
}
}
else
{
lean_dec(v_a_1506_);
lean_dec_ref_known(v___y_1478_, 3);
lean_dec_ref(v_post_1464_);
lean_dec_ref(v_pre_1462_);
return v___x_1507_;
}
}
else
{
lean_dec_ref_known(v___y_1478_, 3);
lean_dec_ref(v_post_1464_);
lean_dec_ref(v_pre_1462_);
return v___x_1505_;
}
}
case 8:
{
lean_object* v_declName_1523_; lean_object* v_type_1524_; lean_object* v_value_1525_; lean_object* v_body_1526_; uint8_t v_nondep_1527_; lean_object* v___x_1528_; 
v_declName_1523_ = lean_ctor_get(v___y_1478_, 0);
v_type_1524_ = lean_ctor_get(v___y_1478_, 1);
v_value_1525_ = lean_ctor_get(v___y_1478_, 2);
v_body_1526_ = lean_ctor_get(v___y_1478_, 3);
v_nondep_1527_ = lean_ctor_get_uint8(v___y_1478_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_1524_);
lean_inc_ref(v_post_1464_);
lean_inc_ref(v_pre_1462_);
v___x_1528_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1462_, v_post_1464_, v_type_1524_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
if (lean_obj_tag(v___x_1528_) == 0)
{
lean_object* v_a_1529_; lean_object* v___x_1530_; 
v_a_1529_ = lean_ctor_get(v___x_1528_, 0);
lean_inc(v_a_1529_);
lean_dec_ref_known(v___x_1528_, 1);
lean_inc_ref(v_value_1525_);
lean_inc_ref(v_post_1464_);
lean_inc_ref(v_pre_1462_);
v___x_1530_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1462_, v_post_1464_, v_value_1525_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
if (lean_obj_tag(v___x_1530_) == 0)
{
lean_object* v_a_1531_; lean_object* v___x_1532_; 
v_a_1531_ = lean_ctor_get(v___x_1530_, 0);
lean_inc(v_a_1531_);
lean_dec_ref_known(v___x_1530_, 1);
lean_inc_ref(v_body_1526_);
lean_inc_ref(v_post_1464_);
lean_inc_ref(v_pre_1462_);
v___x_1532_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1462_, v_post_1464_, v_body_1526_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
if (lean_obj_tag(v___x_1532_) == 0)
{
lean_object* v_a_1533_; size_t v___x_1534_; size_t v___x_1535_; uint8_t v___x_1536_; 
v_a_1533_ = lean_ctor_get(v___x_1532_, 0);
lean_inc(v_a_1533_);
lean_dec_ref_known(v___x_1532_, 1);
v___x_1534_ = lean_ptr_addr(v_type_1524_);
v___x_1535_ = lean_ptr_addr(v_a_1529_);
v___x_1536_ = lean_usize_dec_eq(v___x_1534_, v___x_1535_);
if (v___x_1536_ == 0)
{
lean_object* v___x_1537_; lean_object* v___x_1538_; 
lean_inc(v_declName_1523_);
lean_dec_ref_known(v___y_1478_, 4);
v___x_1537_ = l_Lean_Expr_letE___override(v_declName_1523_, v_a_1529_, v_a_1531_, v_a_1533_, v_nondep_1527_);
v___x_1538_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1462_, v_post_1464_, v___x_1537_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
return v___x_1538_;
}
else
{
size_t v___x_1539_; size_t v___x_1540_; uint8_t v___x_1541_; 
v___x_1539_ = lean_ptr_addr(v_value_1525_);
v___x_1540_ = lean_ptr_addr(v_a_1531_);
v___x_1541_ = lean_usize_dec_eq(v___x_1539_, v___x_1540_);
if (v___x_1541_ == 0)
{
lean_object* v___x_1542_; lean_object* v___x_1543_; 
lean_inc(v_declName_1523_);
lean_dec_ref_known(v___y_1478_, 4);
v___x_1542_ = l_Lean_Expr_letE___override(v_declName_1523_, v_a_1529_, v_a_1531_, v_a_1533_, v_nondep_1527_);
v___x_1543_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1462_, v_post_1464_, v___x_1542_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
return v___x_1543_;
}
else
{
size_t v___x_1544_; size_t v___x_1545_; uint8_t v___x_1546_; 
v___x_1544_ = lean_ptr_addr(v_body_1526_);
v___x_1545_ = lean_ptr_addr(v_a_1533_);
v___x_1546_ = lean_usize_dec_eq(v___x_1544_, v___x_1545_);
if (v___x_1546_ == 0)
{
lean_object* v___x_1547_; lean_object* v___x_1548_; 
lean_inc(v_declName_1523_);
lean_dec_ref_known(v___y_1478_, 4);
v___x_1547_ = l_Lean_Expr_letE___override(v_declName_1523_, v_a_1529_, v_a_1531_, v_a_1533_, v_nondep_1527_);
v___x_1548_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1462_, v_post_1464_, v___x_1547_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
return v___x_1548_;
}
else
{
lean_object* v___x_1549_; 
lean_dec(v_a_1533_);
lean_dec(v_a_1531_);
lean_dec(v_a_1529_);
v___x_1549_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1462_, v_post_1464_, v___y_1478_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
return v___x_1549_;
}
}
}
}
else
{
lean_dec(v_a_1531_);
lean_dec(v_a_1529_);
lean_dec_ref_known(v___y_1478_, 4);
lean_dec_ref(v_post_1464_);
lean_dec_ref(v_pre_1462_);
return v___x_1532_;
}
}
else
{
lean_dec(v_a_1529_);
lean_dec_ref_known(v___y_1478_, 4);
lean_dec_ref(v_post_1464_);
lean_dec_ref(v_pre_1462_);
return v___x_1530_;
}
}
else
{
lean_dec_ref_known(v___y_1478_, 4);
lean_dec_ref(v_post_1464_);
lean_dec_ref(v_pre_1462_);
return v___x_1528_;
}
}
case 5:
{
lean_object* v_dummy_1550_; lean_object* v_nargs_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; 
v_dummy_1550_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__1___closed__0);
v_nargs_1551_ = l_Lean_Expr_getAppNumArgs(v___y_1478_);
lean_inc(v_nargs_1551_);
v___x_1552_ = lean_mk_array(v_nargs_1551_, v_dummy_1550_);
v___x_1553_ = lean_unsigned_to_nat(1u);
v___x_1554_ = lean_nat_sub(v_nargs_1551_, v___x_1553_);
lean_dec(v_nargs_1551_);
v___x_1555_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__4(v_pre_1462_, v_post_1464_, v___y_1478_, v___x_1552_, v___x_1554_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
return v___x_1555_;
}
case 10:
{
lean_object* v_data_1556_; lean_object* v_expr_1557_; lean_object* v___x_1558_; 
v_data_1556_ = lean_ctor_get(v___y_1478_, 0);
v_expr_1557_ = lean_ctor_get(v___y_1478_, 1);
lean_inc_ref(v_expr_1557_);
lean_inc_ref(v_post_1464_);
lean_inc_ref(v_pre_1462_);
v___x_1558_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1462_, v_post_1464_, v_expr_1557_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
if (lean_obj_tag(v___x_1558_) == 0)
{
lean_object* v_a_1559_; size_t v___x_1560_; size_t v___x_1561_; uint8_t v___x_1562_; 
v_a_1559_ = lean_ctor_get(v___x_1558_, 0);
lean_inc(v_a_1559_);
lean_dec_ref_known(v___x_1558_, 1);
v___x_1560_ = lean_ptr_addr(v_expr_1557_);
v___x_1561_ = lean_ptr_addr(v_a_1559_);
v___x_1562_ = lean_usize_dec_eq(v___x_1560_, v___x_1561_);
if (v___x_1562_ == 0)
{
lean_object* v___x_1563_; lean_object* v___x_1564_; 
lean_inc(v_data_1556_);
lean_dec_ref_known(v___y_1478_, 2);
v___x_1563_ = l_Lean_Expr_mdata___override(v_data_1556_, v_a_1559_);
v___x_1564_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1462_, v_post_1464_, v___x_1563_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
return v___x_1564_;
}
else
{
lean_object* v___x_1565_; 
lean_dec(v_a_1559_);
v___x_1565_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1462_, v_post_1464_, v___y_1478_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
return v___x_1565_;
}
}
else
{
lean_dec_ref_known(v___y_1478_, 2);
lean_dec_ref(v_post_1464_);
lean_dec_ref(v_pre_1462_);
return v___x_1558_;
}
}
case 11:
{
lean_object* v_typeName_1566_; lean_object* v_idx_1567_; lean_object* v_struct_1568_; lean_object* v___x_1569_; 
v_typeName_1566_ = lean_ctor_get(v___y_1478_, 0);
v_idx_1567_ = lean_ctor_get(v___y_1478_, 1);
v_struct_1568_ = lean_ctor_get(v___y_1478_, 2);
lean_inc_ref(v_struct_1568_);
lean_inc_ref(v_post_1464_);
lean_inc_ref(v_pre_1462_);
v___x_1569_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1462_, v_post_1464_, v_struct_1568_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
if (lean_obj_tag(v___x_1569_) == 0)
{
lean_object* v_a_1570_; size_t v___x_1571_; size_t v___x_1572_; uint8_t v___x_1573_; 
v_a_1570_ = lean_ctor_get(v___x_1569_, 0);
lean_inc(v_a_1570_);
lean_dec_ref_known(v___x_1569_, 1);
v___x_1571_ = lean_ptr_addr(v_struct_1568_);
v___x_1572_ = lean_ptr_addr(v_a_1570_);
v___x_1573_ = lean_usize_dec_eq(v___x_1571_, v___x_1572_);
if (v___x_1573_ == 0)
{
lean_object* v___x_1574_; lean_object* v___x_1575_; 
lean_inc(v_idx_1567_);
lean_inc(v_typeName_1566_);
lean_dec_ref_known(v___y_1478_, 3);
v___x_1574_ = l_Lean_Expr_proj___override(v_typeName_1566_, v_idx_1567_, v_a_1570_);
v___x_1575_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1462_, v_post_1464_, v___x_1574_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
return v___x_1575_;
}
else
{
lean_object* v___x_1576_; 
lean_dec(v_a_1570_);
v___x_1576_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1462_, v_post_1464_, v___y_1478_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
return v___x_1576_;
}
}
else
{
lean_dec_ref_known(v___y_1478_, 3);
lean_dec_ref(v_post_1464_);
lean_dec_ref(v_pre_1462_);
return v___x_1569_;
}
}
default: 
{
lean_object* v___x_1577_; 
v___x_1577_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1462_, v_post_1464_, v___y_1478_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
return v___x_1577_;
}
}
}
}
}
else
{
lean_object* v_a_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1596_; 
lean_dec_ref(v_post_1464_);
lean_dec_ref(v_e_1463_);
lean_dec_ref(v_pre_1462_);
v_a_1589_ = lean_ctor_get(v___x_1472_, 0);
v_isSharedCheck_1596_ = !lean_is_exclusive(v___x_1472_);
if (v_isSharedCheck_1596_ == 0)
{
v___x_1591_ = v___x_1472_;
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_a_1589_);
lean_dec(v___x_1472_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v___x_1594_; 
if (v_isShared_1592_ == 0)
{
v___x_1594_ = v___x_1591_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v_a_1589_);
v___x_1594_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
return v___x_1594_;
}
}
}
}
else
{
lean_object* v_a_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1604_; 
lean_dec_ref(v_post_1464_);
lean_dec_ref(v_e_1463_);
lean_dec_ref(v_pre_1462_);
v_a_1597_ = lean_ctor_get(v___x_1471_, 0);
v_isSharedCheck_1604_ = !lean_is_exclusive(v___x_1471_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1599_ = v___x_1471_;
v_isShared_1600_ = v_isSharedCheck_1604_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_a_1597_);
lean_dec(v___x_1471_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1604_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v___x_1602_; 
if (v_isShared_1600_ == 0)
{
v___x_1602_ = v___x_1599_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_a_1597_);
v___x_1602_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
return v___x_1602_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1461_ = stack[0].m_obj;
lean_object* v_pre_1462_ = stack[1].m_obj;
lean_object* v_e_1463_ = stack[2].m_obj;
lean_object* v_post_1464_ = stack[3].m_obj;
lean_object* v___y_1465_ = stack[4].m_obj;
lean_object* v___y_1466_ = stack[5].m_obj;
lean_object* v___y_1467_ = stack[6].m_obj;
lean_object* v___y_1468_ = stack[7].m_obj;
lean_object* v___y_1469_ = stack[8].m_obj;
lean_object* v_res_1605_;
v_res_1605_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__1(v___x_1461_, v_pre_1462_, v_e_1463_, v_post_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
stack->m_obj
 = v_res_1605_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__1___boxed(lean_object* v___x_1606_, lean_object* v_pre_1607_, lean_object* v_e_1608_, lean_object* v_post_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_){
_start:
{
lean_object* v_res_1616_; 
v_res_1616_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__1(v___x_1606_, v_pre_1607_, v_e_1608_, v_post_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_);
lean_dec(v___y_1614_);
lean_dec_ref(v___y_1613_);
lean_dec(v___y_1612_);
lean_dec_ref(v___y_1611_);
lean_dec(v___y_1610_);
return v_res_1616_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(lean_object* v_pre_1617_, lean_object* v_post_1618_, lean_object* v_e_1619_, lean_object* v_a_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_){
_start:
{
lean_object* v___x_1626_; lean_object* v___x_1627_; 
lean_inc(v_a_1620_);
v___x_1626_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1626_, 0, lean_box(0));
lean_closure_set(v___x_1626_, 1, lean_box(0));
lean_closure_set(v___x_1626_, 2, v_a_1620_);
v___x_1627_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__0(lean_box(0), v___x_1626_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_);
if (lean_obj_tag(v___x_1627_) == 0)
{
lean_object* v_a_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1659_; 
v_a_1628_ = lean_ctor_get(v___x_1627_, 0);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1627_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1630_ = v___x_1627_;
v_isShared_1631_ = v_isSharedCheck_1659_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_a_1628_);
lean_dec(v___x_1627_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1659_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v___x_1632_; 
v___x_1632_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3___redArg(v_a_1628_, v_e_1619_);
lean_dec(v_a_1628_);
if (lean_obj_tag(v___x_1632_) == 0)
{
lean_object* v___x_1633_; lean_object* v___f_1634_; lean_object* v___x_1635_; 
lean_del_object(v___x_1630_);
v___x_1633_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___closed__0));
lean_inc_ref(v_e_1619_);
v___f_1634_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__1___boxed), 10, 4);
lean_closure_set(v___f_1634_, 0, v___x_1633_);
lean_closure_set(v___f_1634_, 1, v_pre_1617_);
lean_closure_set(v___f_1634_, 2, v_e_1619_);
lean_closure_set(v___f_1634_, 3, v_post_1618_);
v___x_1635_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5___redArg(v___f_1634_, v_a_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_);
if (lean_obj_tag(v___x_1635_) == 0)
{
lean_object* v_a_1636_; lean_object* v___f_1637_; lean_object* v___x_1638_; 
v_a_1636_ = lean_ctor_get(v___x_1635_, 0);
lean_inc_n(v_a_1636_, 2);
lean_dec_ref_known(v___x_1635_, 1);
lean_inc(v_a_1620_);
v___f_1637_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1637_, 0, v_a_1620_);
lean_closure_set(v___f_1637_, 1, v_e_1619_);
lean_closure_set(v___f_1637_, 2, v_a_1636_);
v___x_1638_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__0(lean_box(0), v___f_1637_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_);
if (lean_obj_tag(v___x_1638_) == 0)
{
lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1645_; 
v_isSharedCheck_1645_ = !lean_is_exclusive(v___x_1638_);
if (v_isSharedCheck_1645_ == 0)
{
lean_object* v_unused_1646_; 
v_unused_1646_ = lean_ctor_get(v___x_1638_, 0);
lean_dec(v_unused_1646_);
v___x_1640_ = v___x_1638_;
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
else
{
lean_dec(v___x_1638_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1643_; 
if (v_isShared_1641_ == 0)
{
lean_ctor_set(v___x_1640_, 0, v_a_1636_);
v___x_1643_ = v___x_1640_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_a_1636_);
v___x_1643_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
return v___x_1643_;
}
}
}
else
{
lean_object* v_a_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1654_; 
lean_dec(v_a_1636_);
v_a_1647_ = lean_ctor_get(v___x_1638_, 0);
v_isSharedCheck_1654_ = !lean_is_exclusive(v___x_1638_);
if (v_isSharedCheck_1654_ == 0)
{
v___x_1649_ = v___x_1638_;
v_isShared_1650_ = v_isSharedCheck_1654_;
goto v_resetjp_1648_;
}
else
{
lean_inc(v_a_1647_);
lean_dec(v___x_1638_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1654_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
lean_object* v___x_1652_; 
if (v_isShared_1650_ == 0)
{
v___x_1652_ = v___x_1649_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v_a_1647_);
v___x_1652_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
return v___x_1652_;
}
}
}
}
else
{
lean_dec_ref(v_e_1619_);
return v___x_1635_;
}
}
else
{
lean_object* v_val_1655_; lean_object* v___x_1657_; 
lean_dec_ref(v_e_1619_);
lean_dec_ref(v_post_1618_);
lean_dec_ref(v_pre_1617_);
v_val_1655_ = lean_ctor_get(v___x_1632_, 0);
lean_inc(v_val_1655_);
lean_dec_ref_known(v___x_1632_, 1);
if (v_isShared_1631_ == 0)
{
lean_ctor_set(v___x_1630_, 0, v_val_1655_);
v___x_1657_ = v___x_1630_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_val_1655_);
v___x_1657_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
return v___x_1657_;
}
}
}
}
else
{
lean_object* v_a_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1667_; 
lean_dec_ref(v_e_1619_);
lean_dec_ref(v_post_1618_);
lean_dec_ref(v_pre_1617_);
v_a_1660_ = lean_ctor_get(v___x_1627_, 0);
v_isSharedCheck_1667_ = !lean_is_exclusive(v___x_1627_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1662_ = v___x_1627_;
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_a_1660_);
lean_dec(v___x_1627_);
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
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_1617_ = stack[0].m_obj;
lean_object* v_post_1618_ = stack[1].m_obj;
lean_object* v_e_1619_ = stack[2].m_obj;
lean_object* v_a_1620_ = stack[3].m_obj;
lean_object* v___y_1621_ = stack[4].m_obj;
lean_object* v___y_1622_ = stack[5].m_obj;
lean_object* v___y_1623_ = stack[6].m_obj;
lean_object* v___y_1624_ = stack[7].m_obj;
lean_object* v_res_1668_;
v_res_1668_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1617_, v_post_1618_, v_e_1619_, v_a_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_);
stack->m_obj
 = v_res_1668_;
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(lean_object* v_pre_1669_, lean_object* v_post_1670_, lean_object* v_e_1671_, lean_object* v_a_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_){
_start:
{
lean_object* v___x_1678_; 
lean_inc_ref(v_post_1670_);
lean_inc(v___y_1676_);
lean_inc_ref(v___y_1675_);
lean_inc(v___y_1674_);
lean_inc_ref(v___y_1673_);
lean_inc_ref(v_e_1671_);
v___x_1678_ = lean_apply_6(v_post_1670_, v_e_1671_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, lean_box(0));
if (lean_obj_tag(v___x_1678_) == 0)
{
lean_object* v_a_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1697_; 
v_a_1679_ = lean_ctor_get(v___x_1678_, 0);
v_isSharedCheck_1697_ = !lean_is_exclusive(v___x_1678_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1681_ = v___x_1678_;
v_isShared_1682_ = v_isSharedCheck_1697_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_a_1679_);
lean_dec(v___x_1678_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1697_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
switch(lean_obj_tag(v_a_1679_))
{
case 0:
{
lean_object* v_e_1683_; lean_object* v___x_1685_; 
lean_dec_ref(v_e_1671_);
lean_dec_ref(v_post_1670_);
lean_dec_ref(v_pre_1669_);
v_e_1683_ = lean_ctor_get(v_a_1679_, 0);
lean_inc_ref(v_e_1683_);
lean_dec_ref_known(v_a_1679_, 1);
if (v_isShared_1682_ == 0)
{
lean_ctor_set(v___x_1681_, 0, v_e_1683_);
v___x_1685_ = v___x_1681_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v_e_1683_);
v___x_1685_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
return v___x_1685_;
}
}
case 1:
{
lean_object* v_e_1687_; lean_object* v___x_1688_; 
lean_del_object(v___x_1681_);
lean_dec_ref(v_e_1671_);
v_e_1687_ = lean_ctor_get(v_a_1679_, 0);
lean_inc_ref(v_e_1687_);
lean_dec_ref_known(v_a_1679_, 1);
v___x_1688_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1669_, v_post_1670_, v_e_1687_, v_a_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_);
return v___x_1688_;
}
default: 
{
lean_object* v_e_x3f_1689_; 
lean_dec_ref(v_post_1670_);
lean_dec_ref(v_pre_1669_);
v_e_x3f_1689_ = lean_ctor_get(v_a_1679_, 0);
lean_inc(v_e_x3f_1689_);
lean_dec_ref_known(v_a_1679_, 1);
if (lean_obj_tag(v_e_x3f_1689_) == 0)
{
lean_object* v___x_1691_; 
if (v_isShared_1682_ == 0)
{
lean_ctor_set(v___x_1681_, 0, v_e_1671_);
v___x_1691_ = v___x_1681_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_e_1671_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
return v___x_1691_;
}
}
else
{
lean_object* v_val_1693_; lean_object* v___x_1695_; 
lean_dec_ref(v_e_1671_);
v_val_1693_ = lean_ctor_get(v_e_x3f_1689_, 0);
lean_inc(v_val_1693_);
lean_dec_ref_known(v_e_x3f_1689_, 1);
if (v_isShared_1682_ == 0)
{
lean_ctor_set(v___x_1681_, 0, v_val_1693_);
v___x_1695_ = v___x_1681_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v_val_1693_);
v___x_1695_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
return v___x_1695_;
}
}
}
}
}
}
else
{
lean_object* v_a_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1705_; 
lean_dec_ref(v_e_1671_);
lean_dec_ref(v_post_1670_);
lean_dec_ref(v_pre_1669_);
v_a_1698_ = lean_ctor_get(v___x_1678_, 0);
v_isSharedCheck_1705_ = !lean_is_exclusive(v___x_1678_);
if (v_isSharedCheck_1705_ == 0)
{
v___x_1700_ = v___x_1678_;
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_a_1698_);
lean_dec(v___x_1678_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v___x_1703_; 
if (v_isShared_1701_ == 0)
{
v___x_1703_ = v___x_1700_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v_a_1698_);
v___x_1703_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
return v___x_1703_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_1669_ = stack[0].m_obj;
lean_object* v_post_1670_ = stack[1].m_obj;
lean_object* v_e_1671_ = stack[2].m_obj;
lean_object* v_a_1672_ = stack[3].m_obj;
lean_object* v___y_1673_ = stack[4].m_obj;
lean_object* v___y_1674_ = stack[5].m_obj;
lean_object* v___y_1675_ = stack[6].m_obj;
lean_object* v___y_1676_ = stack[7].m_obj;
lean_object* v_res_1706_;
v_res_1706_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1669_, v_post_1670_, v_e_1671_, v_a_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_);
stack->m_obj
 = v_res_1706_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_1707_, lean_object* v_post_1708_, lean_object* v_e_1709_, lean_object* v_a_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_){
_start:
{
lean_object* v_res_1716_; 
v_res_1716_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1707_, v_post_1708_, v_e_1709_, v_a_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
lean_dec(v___y_1714_);
lean_dec_ref(v___y_1713_);
lean_dec(v___y_1712_);
lean_dec_ref(v___y_1711_);
lean_dec(v_a_1710_);
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_1717_, lean_object* v_post_1718_, lean_object* v_sz_1719_, lean_object* v_i_1720_, lean_object* v_bs_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_){
_start:
{
size_t v_sz_boxed_1728_; size_t v_i_boxed_1729_; lean_object* v_res_1730_; 
v_sz_boxed_1728_ = lean_unbox_usize(v_sz_1719_);
lean_dec(v_sz_1719_);
v_i_boxed_1729_ = lean_unbox_usize(v_i_1720_);
lean_dec(v_i_1720_);
v_res_1730_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__1(v_pre_1717_, v_post_1718_, v_sz_boxed_1728_, v_i_boxed_1729_, v_bs_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_);
lean_dec(v___y_1726_);
lean_dec_ref(v___y_1725_);
lean_dec(v___y_1724_);
lean_dec_ref(v___y_1723_);
lean_dec(v___y_1722_);
return v_res_1730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__4___boxed(lean_object* v_pre_1731_, lean_object* v_post_1732_, lean_object* v_x_1733_, lean_object* v_x_1734_, lean_object* v_x_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_){
_start:
{
lean_object* v_res_1742_; 
v_res_1742_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__4(v_pre_1731_, v_post_1732_, v_x_1733_, v_x_1734_, v_x_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
lean_dec(v___y_1736_);
return v_res_1742_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___boxed(lean_object* v_pre_1743_, lean_object* v_post_1744_, lean_object* v_e_1745_, lean_object* v_a_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_){
_start:
{
lean_object* v_res_1752_; 
v_res_1752_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1743_, v_post_1744_, v_e_1745_, v_a_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
lean_dec(v___y_1750_);
lean_dec_ref(v___y_1749_);
lean_dec(v___y_1748_);
lean_dec_ref(v___y_1747_);
lean_dec(v_a_1746_);
return v_res_1752_;
}
}
lean_object* l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___lam__0(lean_object* v_00_u03b1_1753_, lean_object* v_x_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_){
_start:
{
lean_object* v___x_1760_; lean_object* v___x_1761_; 
v___x_1760_ = lean_apply_1(v_x_1754_, lean_box(0));
v___x_1761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1761_, 0, v___x_1760_);
return v___x_1761_;
}
}
LEAN_EXPORT void l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1754_ = stack[1].m_obj;
lean_object* v___y_1755_ = stack[2].m_obj;
lean_object* v___y_1756_ = stack[3].m_obj;
lean_object* v___y_1757_ = stack[4].m_obj;
lean_object* v___y_1758_ = stack[5].m_obj;
lean_object* v_res_1762_;
v_res_1762_ = l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___lam__0(lean_box(0), v_x_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_);
stack->m_obj
 = v_res_1762_;
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___lam__0___boxed(lean_object* v_00_u03b1_1763_, lean_object* v_x_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_){
_start:
{
lean_object* v_res_1770_; 
v_res_1770_ = l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___lam__0(v_00_u03b1_1763_, v_x_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_);
lean_dec(v___y_1768_);
lean_dec_ref(v___y_1767_);
lean_dec(v___y_1766_);
lean_dec_ref(v___y_1765_);
return v_res_1770_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; 
v___x_1771_ = lean_box(0);
v___x_1772_ = lean_unsigned_to_nat(16u);
v___x_1773_ = lean_mk_array(v___x_1772_, v___x_1771_);
return v___x_1773_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; 
v___x_1774_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__0, &l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__0_once, _init_l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__0);
v___x_1775_ = lean_unsigned_to_nat(0u);
v___x_1776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1776_, 0, v___x_1775_);
lean_ctor_set(v___x_1776_, 1, v___x_1774_);
return v___x_1776_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1777_; lean_object* v___x_1778_; 
v___x_1777_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__1, &l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__1_once, _init_l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__1);
v___x_1778_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1778_, 0, lean_box(0));
lean_closure_set(v___x_1778_, 1, lean_box(0));
lean_closure_set(v___x_1778_, 2, v___x_1777_);
return v___x_1778_;
}
}
lean_object* l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0(lean_object* v_input_1779_, lean_object* v_pre_1780_, lean_object* v_post_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_){
_start:
{
lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v_a_1789_; lean_object* v___x_1790_; 
v___x_1787_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__2, &l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__2_once, _init_l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__2);
v___x_1788_ = l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___lam__0(lean_box(0), v___x_1787_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_);
v_a_1789_ = lean_ctor_get(v___x_1788_, 0);
lean_inc(v_a_1789_);
lean_dec_ref(v___x_1788_);
v___x_1790_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1780_, v_post_1781_, v_input_1779_, v_a_1789_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_);
if (lean_obj_tag(v___x_1790_) == 0)
{
lean_object* v_a_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1800_; 
v_a_1791_ = lean_ctor_get(v___x_1790_, 0);
lean_inc(v_a_1791_);
lean_dec_ref_known(v___x_1790_, 1);
v___x_1792_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1792_, 0, lean_box(0));
lean_closure_set(v___x_1792_, 1, lean_box(0));
lean_closure_set(v___x_1792_, 2, v_a_1789_);
v___x_1793_ = l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___lam__0(lean_box(0), v___x_1792_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_);
v_isSharedCheck_1800_ = !lean_is_exclusive(v___x_1793_);
if (v_isSharedCheck_1800_ == 0)
{
lean_object* v_unused_1801_; 
v_unused_1801_ = lean_ctor_get(v___x_1793_, 0);
lean_dec(v_unused_1801_);
v___x_1795_ = v___x_1793_;
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
else
{
lean_dec(v___x_1793_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v___x_1798_; 
if (v_isShared_1796_ == 0)
{
lean_ctor_set(v___x_1795_, 0, v_a_1791_);
v___x_1798_ = v___x_1795_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v_a_1791_);
v___x_1798_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
return v___x_1798_;
}
}
}
else
{
lean_dec(v_a_1789_);
return v___x_1790_;
}
}
}
LEAN_EXPORT void l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_input_1779_ = stack[0].m_obj;
lean_object* v_pre_1780_ = stack[1].m_obj;
lean_object* v_post_1781_ = stack[2].m_obj;
lean_object* v___y_1782_ = stack[3].m_obj;
lean_object* v___y_1783_ = stack[4].m_obj;
lean_object* v___y_1784_ = stack[5].m_obj;
lean_object* v___y_1785_ = stack[6].m_obj;
lean_object* v_res_1802_;
v_res_1802_ = l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0(v_input_1779_, v_pre_1780_, v_post_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_);
stack->m_obj
 = v_res_1802_;
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___boxed(lean_object* v_input_1803_, lean_object* v_pre_1804_, lean_object* v_post_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_){
_start:
{
lean_object* v_res_1811_; 
v_res_1811_ = l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0(v_input_1803_, v_pre_1804_, v_post_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_);
lean_dec(v___y_1809_);
lean_dec_ref(v___y_1808_);
lean_dec(v___y_1807_);
lean_dec_ref(v___y_1806_);
return v_res_1811_;
}
}
lean_object* l_Lean_Meta_PProdN_reduceProjs(lean_object* v_e_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_){
_start:
{
lean_object* v___f_1820_; lean_object* v___f_1821_; lean_object* v___x_1822_; 
v___f_1820_ = ((lean_object*)(l_Lean_Meta_PProdN_reduceProjs___closed__0));
v___f_1821_ = ((lean_object*)(l_Lean_Meta_PProdN_reduceProjs___closed__1));
v___x_1822_ = l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0(v_e_1814_, v___f_1820_, v___f_1821_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_);
return v___x_1822_;
}
}
LEAN_EXPORT void l_Lean_Meta_PProdN_reduceProjs_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1814_ = stack[0].m_obj;
lean_object* v_a_1815_ = stack[1].m_obj;
lean_object* v_a_1816_ = stack[2].m_obj;
lean_object* v_a_1817_ = stack[3].m_obj;
lean_object* v_a_1818_ = stack[4].m_obj;
lean_object* v_res_1823_;
v_res_1823_ = l_Lean_Meta_PProdN_reduceProjs(v_e_1814_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_);
stack->m_obj
 = v_res_1823_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_reduceProjs___boxed(lean_object* v_e_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_){
_start:
{
lean_object* v_res_1830_; 
v_res_1830_ = l_Lean_Meta_PProdN_reduceProjs(v_e_1824_, v_a_1825_, v_a_1826_, v_a_1827_, v_a_1828_);
lean_dec(v_a_1828_);
lean_dec_ref(v_a_1827_);
lean_dec(v_a_1826_);
lean_dec_ref(v_a_1825_);
return v_res_1830_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_1831_, lean_object* v_m_1832_, lean_object* v_a_1833_){
_start:
{
lean_object* v___x_1834_; 
v___x_1834_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3___redArg(v_m_1832_, v_a_1833_);
return v___x_1834_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_1835_, lean_object* v_m_1836_, lean_object* v_a_1837_){
_start:
{
lean_object* v_res_1838_; 
v_res_1838_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3(v_00_u03b2_1835_, v_m_1836_, v_a_1837_);
lean_dec_ref(v_a_1837_);
lean_dec_ref(v_m_1836_);
return v_res_1838_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_1839_, lean_object* v_ref_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_){
_start:
{
lean_object* v___x_1844_; 
v___x_1844_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_1840_);
return v___x_1844_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1840_ = stack[1].m_obj;
lean_object* v___y_1841_ = stack[2].m_obj;
lean_object* v___y_1842_ = stack[3].m_obj;
lean_object* v_res_1845_;
v_res_1845_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7(lean_box(0), v_ref_1840_, v___y_1841_, v___y_1842_);
stack->m_obj
 = v_res_1845_;
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
lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__8(lean_object* v_00_u03b1_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_){
_start:
{
lean_object* v___x_1856_; 
v___x_1856_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__8___redArg();
return v___x_1856_;
}
}
LEAN_EXPORT void l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1853_ = stack[1].m_obj;
lean_object* v___y_1854_ = stack[2].m_obj;
lean_object* v_res_1857_;
v_res_1857_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__8(lean_box(0), v___y_1853_, v___y_1854_);
stack->m_obj
 = v_res_1857_;
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__8___boxed(lean_object* v_00_u03b1_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_){
_start:
{
lean_object* v_res_1862_; 
v_res_1862_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__8(v_00_u03b1_1858_, v___y_1859_, v___y_1860_);
lean_dec(v___y_1860_);
lean_dec_ref(v___y_1859_);
return v_res_1862_;
}
}
lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5(lean_object* v_00_u03b1_1863_, lean_object* v_x_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_){
_start:
{
lean_object* v___x_1871_; 
v___x_1871_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5___redArg(v_x_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_);
return v___x_1871_;
}
}
LEAN_EXPORT void l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1864_ = stack[1].m_obj;
lean_object* v___y_1865_ = stack[2].m_obj;
lean_object* v___y_1866_ = stack[3].m_obj;
lean_object* v___y_1867_ = stack[4].m_obj;
lean_object* v___y_1868_ = stack[5].m_obj;
lean_object* v___y_1869_ = stack[6].m_obj;
lean_object* v_res_1872_;
v_res_1872_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5(lean_box(0), v_x_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_);
stack->m_obj
 = v_res_1872_;
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b1_1873_, lean_object* v_x_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_){
_start:
{
lean_object* v_res_1881_; 
v_res_1881_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5(v_00_u03b1_1873_, v_x_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_);
lean_dec(v___y_1879_);
lean_dec_ref(v___y_1878_);
lean_dec(v___y_1877_);
lean_dec_ref(v___y_1876_);
lean_dec(v___y_1875_);
return v_res_1881_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6(lean_object* v_00_u03b2_1882_, lean_object* v_m_1883_, lean_object* v_a_1884_, lean_object* v_b_1885_){
_start:
{
lean_object* v___x_1886_; 
v___x_1886_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6___redArg(v_m_1883_, v_a_1884_, v_b_1885_);
return v___x_1886_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b2_1887_, lean_object* v_a_1888_, lean_object* v_x_1889_){
_start:
{
lean_object* v___x_1890_; 
v___x_1890_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3_spec__4___redArg(v_a_1888_, v_x_1889_);
return v___x_1890_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3_spec__4___boxed(lean_object* v_00_u03b2_1891_, lean_object* v_a_1892_, lean_object* v_x_1893_){
_start:
{
lean_object* v_res_1894_; 
v_res_1894_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3_spec__4(v_00_u03b2_1891_, v_a_1892_, v_x_1893_);
lean_dec(v_x_1893_);
lean_dec_ref(v_a_1892_);
return v_res_1894_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__10(lean_object* v_00_u03b2_1895_, lean_object* v_a_1896_, lean_object* v_x_1897_){
_start:
{
uint8_t v___x_1898_; 
v___x_1898_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__10___redArg(v_a_1896_, v_x_1897_);
return v___x_1898_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1896_ = stack[1].m_obj;
lean_object* v_x_1897_ = stack[2].m_obj;
uint8_t v_res_1899_;
v_res_1899_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__10(lean_box(0), v_a_1896_, v_x_1897_);
stack->m_num = v_res_1899_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__10___boxed(lean_object* v_00_u03b2_1900_, lean_object* v_a_1901_, lean_object* v_x_1902_){
_start:
{
uint8_t v_res_1903_; lean_object* v_r_1904_; 
v_res_1903_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__10(v_00_u03b2_1900_, v_a_1901_, v_x_1902_);
lean_dec(v_x_1902_);
lean_dec_ref(v_a_1901_);
v_r_1904_ = lean_box(v_res_1903_);
return v_r_1904_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11(lean_object* v_00_u03b2_1905_, lean_object* v_data_1906_){
_start:
{
lean_object* v___x_1907_; 
v___x_1907_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11___redArg(v_data_1906_);
return v___x_1907_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__12(lean_object* v_00_u03b2_1908_, lean_object* v_a_1909_, lean_object* v_b_1910_, lean_object* v_x_1911_){
_start:
{
lean_object* v___x_1912_; 
v___x_1912_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__12___redArg(v_a_1909_, v_b_1910_, v_x_1911_);
return v___x_1912_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11_spec__12(lean_object* v_00_u03b2_1913_, lean_object* v_i_1914_, lean_object* v_source_1915_, lean_object* v_target_1916_){
_start:
{
lean_object* v___x_1917_; 
v___x_1917_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v_i_1914_, v_source_1915_, v_target_1916_);
return v___x_1917_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13(lean_object* v_00_u03b2_1918_, lean_object* v_x_1919_, lean_object* v_x_1920_){
_start:
{
lean_object* v___x_1921_; 
v___x_1921_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_x_1919_, v_x_1920_);
return v___x_1921_;
}
}
lean_object* runtime_initialize_Lean_Meta_Transform(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_PProdN(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
