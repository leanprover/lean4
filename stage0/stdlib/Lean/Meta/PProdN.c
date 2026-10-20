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
LEAN_EXPORT lean_object* l_Lean_Meta_mkPProd(lean_object* v_e1_10_, lean_object* v_e2_11_, lean_object* v_a_12_, lean_object* v_a_13_, lean_object* v_a_14_, lean_object* v_a_15_){
_start:
{
lean_object* v___x_17_; 
lean_inc_ref(v_e1_10_);
v___x_17_ = l_Lean_Meta_getLevel(v_e1_10_, v_a_12_, v_a_13_, v_a_14_, v_a_15_);
if (lean_obj_tag(v___x_17_) == 0)
{
lean_object* v_a_18_; lean_object* v___x_20_; uint8_t v_isShared_21_; uint8_t v_isSharedCheck_53_; 
v_a_18_ = lean_ctor_get(v___x_17_, 0);
v_isSharedCheck_53_ = !lean_is_exclusive(v___x_17_);
if (v_isSharedCheck_53_ == 0)
{
v___x_20_ = v___x_17_;
v_isShared_21_ = v_isSharedCheck_53_;
goto v_resetjp_19_;
}
else
{
lean_inc(v_a_18_);
lean_dec(v___x_17_);
v___x_20_ = lean_box(0);
v_isShared_21_ = v_isSharedCheck_53_;
goto v_resetjp_19_;
}
v_resetjp_19_:
{
lean_object* v___x_22_; 
lean_inc_ref(v_e2_11_);
v___x_22_ = l_Lean_Meta_getLevel(v_e2_11_, v_a_12_, v_a_13_, v_a_14_, v_a_15_);
if (lean_obj_tag(v___x_22_) == 0)
{
lean_object* v_a_23_; lean_object* v___x_25_; uint8_t v_isShared_26_; uint8_t v_isSharedCheck_44_; 
v_a_23_ = lean_ctor_get(v___x_22_, 0);
v_isSharedCheck_44_ = !lean_is_exclusive(v___x_22_);
if (v_isSharedCheck_44_ == 0)
{
v___x_25_ = v___x_22_;
v_isShared_26_ = v_isSharedCheck_44_;
goto v_resetjp_24_;
}
else
{
lean_inc(v_a_23_);
lean_dec(v___x_22_);
v___x_25_ = lean_box(0);
v_isShared_26_ = v_isSharedCheck_44_;
goto v_resetjp_24_;
}
v_resetjp_24_:
{
uint8_t v___x_37_; 
v___x_37_ = l_Lean_Level_isAlwaysZero(v_a_18_);
if (v___x_37_ == 0)
{
lean_del_object(v___x_20_);
goto v___jp_27_;
}
else
{
uint8_t v___x_38_; 
v___x_38_ = l_Lean_Level_isAlwaysZero(v_a_23_);
if (v___x_38_ == 0)
{
lean_del_object(v___x_20_);
goto v___jp_27_;
}
else
{
lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_42_; 
lean_del_object(v___x_25_);
lean_dec(v_a_23_);
lean_dec(v_a_18_);
v___x_39_ = lean_obj_once(&l_Lean_Meta_mkPProd___closed__4, &l_Lean_Meta_mkPProd___closed__4_once, _init_l_Lean_Meta_mkPProd___closed__4);
v___x_40_ = l_Lean_mkAppB(v___x_39_, v_e1_10_, v_e2_11_);
if (v_isShared_21_ == 0)
{
lean_ctor_set(v___x_20_, 0, v___x_40_);
v___x_42_ = v___x_20_;
goto v_reusejp_41_;
}
else
{
lean_object* v_reuseFailAlloc_43_; 
v_reuseFailAlloc_43_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_43_, 0, v___x_40_);
v___x_42_ = v_reuseFailAlloc_43_;
goto v_reusejp_41_;
}
v_reusejp_41_:
{
return v___x_42_;
}
}
}
v___jp_27_:
{
lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_35_; 
v___x_28_ = ((lean_object*)(l_Lean_Meta_mkPProd___closed__1));
v___x_29_ = lean_box(0);
v___x_30_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_30_, 0, v_a_23_);
lean_ctor_set(v___x_30_, 1, v___x_29_);
v___x_31_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_31_, 0, v_a_18_);
lean_ctor_set(v___x_31_, 1, v___x_30_);
v___x_32_ = l_Lean_Expr_const___override(v___x_28_, v___x_31_);
v___x_33_ = l_Lean_mkAppB(v___x_32_, v_e1_10_, v_e2_11_);
if (v_isShared_26_ == 0)
{
lean_ctor_set(v___x_25_, 0, v___x_33_);
v___x_35_ = v___x_25_;
goto v_reusejp_34_;
}
else
{
lean_object* v_reuseFailAlloc_36_; 
v_reuseFailAlloc_36_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_36_, 0, v___x_33_);
v___x_35_ = v_reuseFailAlloc_36_;
goto v_reusejp_34_;
}
v_reusejp_34_:
{
return v___x_35_;
}
}
}
}
else
{
lean_object* v_a_45_; lean_object* v___x_47_; uint8_t v_isShared_48_; uint8_t v_isSharedCheck_52_; 
lean_del_object(v___x_20_);
lean_dec(v_a_18_);
lean_dec_ref(v_e2_11_);
lean_dec_ref(v_e1_10_);
v_a_45_ = lean_ctor_get(v___x_22_, 0);
v_isSharedCheck_52_ = !lean_is_exclusive(v___x_22_);
if (v_isSharedCheck_52_ == 0)
{
v___x_47_ = v___x_22_;
v_isShared_48_ = v_isSharedCheck_52_;
goto v_resetjp_46_;
}
else
{
lean_inc(v_a_45_);
lean_dec(v___x_22_);
v___x_47_ = lean_box(0);
v_isShared_48_ = v_isSharedCheck_52_;
goto v_resetjp_46_;
}
v_resetjp_46_:
{
lean_object* v___x_50_; 
if (v_isShared_48_ == 0)
{
v___x_50_ = v___x_47_;
goto v_reusejp_49_;
}
else
{
lean_object* v_reuseFailAlloc_51_; 
v_reuseFailAlloc_51_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_51_, 0, v_a_45_);
v___x_50_ = v_reuseFailAlloc_51_;
goto v_reusejp_49_;
}
v_reusejp_49_:
{
return v___x_50_;
}
}
}
}
}
else
{
lean_object* v_a_54_; lean_object* v___x_56_; uint8_t v_isShared_57_; uint8_t v_isSharedCheck_61_; 
lean_dec_ref(v_e2_11_);
lean_dec_ref(v_e1_10_);
v_a_54_ = lean_ctor_get(v___x_17_, 0);
v_isSharedCheck_61_ = !lean_is_exclusive(v___x_17_);
if (v_isSharedCheck_61_ == 0)
{
v___x_56_ = v___x_17_;
v_isShared_57_ = v_isSharedCheck_61_;
goto v_resetjp_55_;
}
else
{
lean_inc(v_a_54_);
lean_dec(v___x_17_);
v___x_56_ = lean_box(0);
v_isShared_57_ = v_isSharedCheck_61_;
goto v_resetjp_55_;
}
v_resetjp_55_:
{
lean_object* v___x_59_; 
if (v_isShared_57_ == 0)
{
v___x_59_ = v___x_56_;
goto v_reusejp_58_;
}
else
{
lean_object* v_reuseFailAlloc_60_; 
v_reuseFailAlloc_60_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_60_, 0, v_a_54_);
v___x_59_ = v_reuseFailAlloc_60_;
goto v_reusejp_58_;
}
v_reusejp_58_:
{
return v___x_59_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPProd___boxed(lean_object* v_e1_62_, lean_object* v_e2_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l_Lean_Meta_mkPProd(v_e1_62_, v_e2_63_, v_a_64_, v_a_65_, v_a_66_, v_a_67_);
lean_dec(v_a_67_);
lean_dec_ref(v_a_66_);
lean_dec(v_a_65_);
lean_dec_ref(v_a_64_);
return v_res_69_;
}
}
static lean_object* _init_l_Lean_Meta_mkPProdMk___closed__4(void){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_78_ = lean_box(0);
v___x_79_ = ((lean_object*)(l_Lean_Meta_mkPProdMk___closed__3));
v___x_80_ = l_Lean_Expr_const___override(v___x_79_, v___x_78_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPProdMk(lean_object* v_e1_81_, lean_object* v_e2_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_){
_start:
{
lean_object* v___x_88_; 
lean_inc(v_a_86_);
lean_inc_ref(v_a_85_);
lean_inc(v_a_84_);
lean_inc_ref(v_a_83_);
lean_inc_ref(v_e1_81_);
v___x_88_ = lean_infer_type(v_e1_81_, v_a_83_, v_a_84_, v_a_85_, v_a_86_);
if (lean_obj_tag(v___x_88_) == 0)
{
lean_object* v_a_89_; lean_object* v___x_90_; 
v_a_89_ = lean_ctor_get(v___x_88_, 0);
lean_inc(v_a_89_);
lean_dec_ref_known(v___x_88_, 1);
lean_inc(v_a_86_);
lean_inc_ref(v_a_85_);
lean_inc(v_a_84_);
lean_inc_ref(v_a_83_);
lean_inc_ref(v_e2_82_);
v___x_90_ = lean_infer_type(v_e2_82_, v_a_83_, v_a_84_, v_a_85_, v_a_86_);
if (lean_obj_tag(v___x_90_) == 0)
{
lean_object* v_a_91_; lean_object* v___x_92_; 
v_a_91_ = lean_ctor_get(v___x_90_, 0);
lean_inc(v_a_91_);
lean_dec_ref_known(v___x_90_, 1);
lean_inc(v_a_89_);
v___x_92_ = l_Lean_Meta_getLevel(v_a_89_, v_a_83_, v_a_84_, v_a_85_, v_a_86_);
if (lean_obj_tag(v___x_92_) == 0)
{
lean_object* v_a_93_; lean_object* v___x_95_; uint8_t v_isShared_96_; uint8_t v_isSharedCheck_128_; 
v_a_93_ = lean_ctor_get(v___x_92_, 0);
v_isSharedCheck_128_ = !lean_is_exclusive(v___x_92_);
if (v_isSharedCheck_128_ == 0)
{
v___x_95_ = v___x_92_;
v_isShared_96_ = v_isSharedCheck_128_;
goto v_resetjp_94_;
}
else
{
lean_inc(v_a_93_);
lean_dec(v___x_92_);
v___x_95_ = lean_box(0);
v_isShared_96_ = v_isSharedCheck_128_;
goto v_resetjp_94_;
}
v_resetjp_94_:
{
lean_object* v___x_97_; 
lean_inc(v_a_91_);
v___x_97_ = l_Lean_Meta_getLevel(v_a_91_, v_a_83_, v_a_84_, v_a_85_, v_a_86_);
if (lean_obj_tag(v___x_97_) == 0)
{
lean_object* v_a_98_; lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_119_; 
v_a_98_ = lean_ctor_get(v___x_97_, 0);
v_isSharedCheck_119_ = !lean_is_exclusive(v___x_97_);
if (v_isSharedCheck_119_ == 0)
{
v___x_100_ = v___x_97_;
v_isShared_101_ = v_isSharedCheck_119_;
goto v_resetjp_99_;
}
else
{
lean_inc(v_a_98_);
lean_dec(v___x_97_);
v___x_100_ = lean_box(0);
v_isShared_101_ = v_isSharedCheck_119_;
goto v_resetjp_99_;
}
v_resetjp_99_:
{
uint8_t v___x_112_; 
v___x_112_ = l_Lean_Level_isAlwaysZero(v_a_93_);
if (v___x_112_ == 0)
{
lean_del_object(v___x_95_);
goto v___jp_102_;
}
else
{
uint8_t v___x_113_; 
v___x_113_ = l_Lean_Level_isAlwaysZero(v_a_98_);
if (v___x_113_ == 0)
{
lean_del_object(v___x_95_);
goto v___jp_102_;
}
else
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_117_; 
lean_del_object(v___x_100_);
lean_dec(v_a_98_);
lean_dec(v_a_93_);
v___x_114_ = lean_obj_once(&l_Lean_Meta_mkPProdMk___closed__4, &l_Lean_Meta_mkPProdMk___closed__4_once, _init_l_Lean_Meta_mkPProdMk___closed__4);
v___x_115_ = l_Lean_mkApp4(v___x_114_, v_a_89_, v_a_91_, v_e1_81_, v_e2_82_);
if (v_isShared_96_ == 0)
{
lean_ctor_set(v___x_95_, 0, v___x_115_);
v___x_117_ = v___x_95_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v___x_115_);
v___x_117_ = v_reuseFailAlloc_118_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
return v___x_117_;
}
}
}
v___jp_102_:
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_110_; 
v___x_103_ = ((lean_object*)(l_Lean_Meta_mkPProdMk___closed__1));
v___x_104_ = lean_box(0);
v___x_105_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_105_, 0, v_a_98_);
lean_ctor_set(v___x_105_, 1, v___x_104_);
v___x_106_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_106_, 0, v_a_93_);
lean_ctor_set(v___x_106_, 1, v___x_105_);
v___x_107_ = l_Lean_Expr_const___override(v___x_103_, v___x_106_);
v___x_108_ = l_Lean_mkApp4(v___x_107_, v_a_89_, v_a_91_, v_e1_81_, v_e2_82_);
if (v_isShared_101_ == 0)
{
lean_ctor_set(v___x_100_, 0, v___x_108_);
v___x_110_ = v___x_100_;
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
else
{
lean_object* v_a_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_127_; 
lean_del_object(v___x_95_);
lean_dec(v_a_93_);
lean_dec(v_a_91_);
lean_dec(v_a_89_);
lean_dec_ref(v_e2_82_);
lean_dec_ref(v_e1_81_);
v_a_120_ = lean_ctor_get(v___x_97_, 0);
v_isSharedCheck_127_ = !lean_is_exclusive(v___x_97_);
if (v_isSharedCheck_127_ == 0)
{
v___x_122_ = v___x_97_;
v_isShared_123_ = v_isSharedCheck_127_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_a_120_);
lean_dec(v___x_97_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_127_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v___x_125_; 
if (v_isShared_123_ == 0)
{
v___x_125_ = v___x_122_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v_a_120_);
v___x_125_ = v_reuseFailAlloc_126_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
return v___x_125_;
}
}
}
}
}
else
{
lean_object* v_a_129_; lean_object* v___x_131_; uint8_t v_isShared_132_; uint8_t v_isSharedCheck_136_; 
lean_dec(v_a_91_);
lean_dec(v_a_89_);
lean_dec_ref(v_e2_82_);
lean_dec_ref(v_e1_81_);
v_a_129_ = lean_ctor_get(v___x_92_, 0);
v_isSharedCheck_136_ = !lean_is_exclusive(v___x_92_);
if (v_isSharedCheck_136_ == 0)
{
v___x_131_ = v___x_92_;
v_isShared_132_ = v_isSharedCheck_136_;
goto v_resetjp_130_;
}
else
{
lean_inc(v_a_129_);
lean_dec(v___x_92_);
v___x_131_ = lean_box(0);
v_isShared_132_ = v_isSharedCheck_136_;
goto v_resetjp_130_;
}
v_resetjp_130_:
{
lean_object* v___x_134_; 
if (v_isShared_132_ == 0)
{
v___x_134_ = v___x_131_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v_a_129_);
v___x_134_ = v_reuseFailAlloc_135_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
return v___x_134_;
}
}
}
}
else
{
lean_dec(v_a_89_);
lean_dec_ref(v_e2_82_);
lean_dec_ref(v_e1_81_);
return v___x_90_;
}
}
else
{
lean_dec_ref(v_e2_82_);
lean_dec_ref(v_e1_81_);
return v___x_88_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPProdMk___boxed(lean_object* v_e1_137_, lean_object* v_e2_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_Lean_Meta_mkPProdMk(v_e1_137_, v_e2_138_, v_a_139_, v_a_140_, v_a_141_, v_a_142_);
lean_dec(v_a_142_);
lean_dec_ref(v_a_141_);
lean_dec(v_a_140_);
lean_dec_ref(v_a_139_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkPProdFst_spec__0(lean_object* v_msg_145_){
_start:
{
lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_146_ = l_Lean_instInhabitedExpr;
v___x_147_ = lean_panic_fn_borrowed(v___x_146_, v_msg_145_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPProdFst(lean_object* v_t_152_, lean_object* v_e_153_){
_start:
{
lean_object* v___x_168_; uint8_t v___x_169_; 
lean_inc_ref(v_t_152_);
v___x_168_ = l_Lean_Expr_cleanupAnnotations(v_t_152_);
v___x_169_ = l_Lean_Expr_isApp(v___x_168_);
if (v___x_169_ == 0)
{
lean_dec_ref(v___x_168_);
goto v___jp_154_;
}
else
{
lean_object* v___x_170_; uint8_t v___x_171_; 
v___x_170_ = l_Lean_Expr_appFnCleanup___redArg(v___x_168_);
v___x_171_ = l_Lean_Expr_isApp(v___x_170_);
if (v___x_171_ == 0)
{
lean_dec_ref(v___x_170_);
goto v___jp_154_;
}
else
{
lean_object* v___x_172_; lean_object* v___x_173_; uint8_t v___x_174_; 
v___x_172_ = l_Lean_Expr_appFnCleanup___redArg(v___x_170_);
v___x_173_ = ((lean_object*)(l_Lean_Meta_mkPProd___closed__3));
v___x_174_ = l_Lean_Expr_isConstOf(v___x_172_, v___x_173_);
if (v___x_174_ == 0)
{
lean_object* v___x_175_; uint8_t v___x_176_; 
v___x_175_ = ((lean_object*)(l_Lean_Meta_mkPProd___closed__1));
v___x_176_ = l_Lean_Expr_isConstOf(v___x_172_, v___x_175_);
lean_dec_ref(v___x_172_);
if (v___x_176_ == 0)
{
goto v___jp_154_;
}
else
{
lean_object* v___x_177_; lean_object* v___x_178_; 
lean_dec_ref(v_t_152_);
v___x_177_ = lean_unsigned_to_nat(0u);
v___x_178_ = l_Lean_Expr_proj___override(v___x_175_, v___x_177_, v_e_153_);
return v___x_178_;
}
}
else
{
lean_object* v___x_179_; lean_object* v___x_180_; 
lean_dec_ref(v___x_172_);
lean_dec_ref(v_t_152_);
v___x_179_ = lean_unsigned_to_nat(0u);
v___x_180_ = l_Lean_Expr_proj___override(v___x_173_, v___x_179_, v_e_153_);
return v___x_180_;
}
}
}
v___jp_154_:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_155_ = ((lean_object*)(l_Lean_Meta_mkPProdFst___closed__0));
v___x_156_ = ((lean_object*)(l_Lean_Meta_mkPProdFst___closed__1));
v___x_157_ = lean_unsigned_to_nat(60u);
v___x_158_ = lean_unsigned_to_nat(9u);
v___x_159_ = ((lean_object*)(l_Lean_Meta_mkPProdFst___closed__2));
v___x_160_ = lean_expr_dbg_to_string(v_e_153_);
lean_dec_ref(v_e_153_);
v___x_161_ = lean_string_append(v___x_159_, v___x_160_);
lean_dec_ref(v___x_160_);
v___x_162_ = ((lean_object*)(l_Lean_Meta_mkPProdFst___closed__3));
v___x_163_ = lean_string_append(v___x_161_, v___x_162_);
v___x_164_ = lean_expr_dbg_to_string(v_t_152_);
lean_dec_ref(v_t_152_);
v___x_165_ = lean_string_append(v___x_163_, v___x_164_);
lean_dec_ref(v___x_164_);
v___x_166_ = l_mkPanicMessageWithDecl(v___x_155_, v___x_156_, v___x_157_, v___x_158_, v___x_165_);
lean_dec_ref(v___x_165_);
v___x_167_ = l_panic___at___00Lean_Meta_mkPProdFst_spec__0(v___x_166_);
return v___x_167_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPProdFstM(lean_object* v_e_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_){
_start:
{
lean_object* v___x_187_; 
lean_inc(v_a_185_);
lean_inc_ref(v_a_184_);
lean_inc(v_a_183_);
lean_inc_ref(v_a_182_);
lean_inc_ref(v_e_181_);
v___x_187_ = lean_infer_type(v_e_181_, v_a_182_, v_a_183_, v_a_184_, v_a_185_);
if (lean_obj_tag(v___x_187_) == 0)
{
lean_object* v_a_188_; lean_object* v___x_189_; 
v_a_188_ = lean_ctor_get(v___x_187_, 0);
lean_inc(v_a_188_);
lean_dec_ref_known(v___x_187_, 1);
lean_inc(v_a_185_);
lean_inc_ref(v_a_184_);
lean_inc(v_a_183_);
lean_inc_ref(v_a_182_);
v___x_189_ = lean_whnf(v_a_188_, v_a_182_, v_a_183_, v_a_184_, v_a_185_);
if (lean_obj_tag(v___x_189_) == 0)
{
lean_object* v_a_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_198_; 
v_a_190_ = lean_ctor_get(v___x_189_, 0);
v_isSharedCheck_198_ = !lean_is_exclusive(v___x_189_);
if (v_isSharedCheck_198_ == 0)
{
v___x_192_ = v___x_189_;
v_isShared_193_ = v_isSharedCheck_198_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_a_190_);
lean_dec(v___x_189_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_198_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v___x_194_; lean_object* v___x_196_; 
v___x_194_ = l_Lean_Meta_mkPProdFst(v_a_190_, v_e_181_);
if (v_isShared_193_ == 0)
{
lean_ctor_set(v___x_192_, 0, v___x_194_);
v___x_196_ = v___x_192_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v___x_194_);
v___x_196_ = v_reuseFailAlloc_197_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
return v___x_196_;
}
}
}
else
{
lean_dec_ref(v_e_181_);
return v___x_189_;
}
}
else
{
lean_dec_ref(v_e_181_);
return v___x_187_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPProdFstM___boxed(lean_object* v_e_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l_Lean_Meta_mkPProdFstM(v_e_199_, v_a_200_, v_a_201_, v_a_202_, v_a_203_);
lean_dec(v_a_203_);
lean_dec_ref(v_a_202_);
lean_dec(v_a_201_);
lean_dec_ref(v_a_200_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PProdN_0__Lean_Meta_mkTypeSnd(lean_object* v_t_208_){
_start:
{
lean_object* v___x_219_; uint8_t v___x_220_; 
lean_inc_ref(v_t_208_);
v___x_219_ = l_Lean_Expr_cleanupAnnotations(v_t_208_);
v___x_220_ = l_Lean_Expr_isApp(v___x_219_);
if (v___x_220_ == 0)
{
lean_dec_ref(v___x_219_);
goto v___jp_209_;
}
else
{
lean_object* v_arg_221_; lean_object* v___x_222_; uint8_t v___x_223_; 
v_arg_221_ = lean_ctor_get(v___x_219_, 1);
lean_inc_ref(v_arg_221_);
v___x_222_ = l_Lean_Expr_appFnCleanup___redArg(v___x_219_);
v___x_223_ = l_Lean_Expr_isApp(v___x_222_);
if (v___x_223_ == 0)
{
lean_dec_ref(v___x_222_);
lean_dec_ref(v_arg_221_);
goto v___jp_209_;
}
else
{
lean_object* v___x_224_; lean_object* v___x_225_; uint8_t v___x_226_; 
v___x_224_ = l_Lean_Expr_appFnCleanup___redArg(v___x_222_);
v___x_225_ = ((lean_object*)(l_Lean_Meta_mkPProd___closed__3));
v___x_226_ = l_Lean_Expr_isConstOf(v___x_224_, v___x_225_);
if (v___x_226_ == 0)
{
lean_object* v___x_227_; uint8_t v___x_228_; 
v___x_227_ = ((lean_object*)(l_Lean_Meta_mkPProd___closed__1));
v___x_228_ = l_Lean_Expr_isConstOf(v___x_224_, v___x_227_);
lean_dec_ref(v___x_224_);
if (v___x_228_ == 0)
{
lean_dec_ref(v_arg_221_);
goto v___jp_209_;
}
else
{
lean_dec_ref(v_t_208_);
return v_arg_221_;
}
}
else
{
lean_dec_ref(v___x_224_);
lean_dec_ref(v_t_208_);
return v_arg_221_;
}
}
}
v___jp_209_:
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_210_ = ((lean_object*)(l_Lean_Meta_mkPProdFst___closed__0));
v___x_211_ = ((lean_object*)(l___private_Lean_Meta_PProdN_0__Lean_Meta_mkTypeSnd___closed__0));
v___x_212_ = lean_unsigned_to_nat(70u);
v___x_213_ = lean_unsigned_to_nat(9u);
v___x_214_ = ((lean_object*)(l___private_Lean_Meta_PProdN_0__Lean_Meta_mkTypeSnd___closed__1));
v___x_215_ = lean_expr_dbg_to_string(v_t_208_);
lean_dec_ref(v_t_208_);
v___x_216_ = lean_string_append(v___x_214_, v___x_215_);
lean_dec_ref(v___x_215_);
v___x_217_ = l_mkPanicMessageWithDecl(v___x_210_, v___x_211_, v___x_212_, v___x_213_, v___x_216_);
lean_dec_ref(v___x_216_);
v___x_218_ = l_panic___at___00Lean_Meta_mkPProdFst_spec__0(v___x_217_);
return v___x_218_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPProdSnd(lean_object* v_t_231_, lean_object* v_e_232_){
_start:
{
lean_object* v___x_247_; uint8_t v___x_248_; 
lean_inc_ref(v_t_231_);
v___x_247_ = l_Lean_Expr_cleanupAnnotations(v_t_231_);
v___x_248_ = l_Lean_Expr_isApp(v___x_247_);
if (v___x_248_ == 0)
{
lean_dec_ref(v___x_247_);
goto v___jp_233_;
}
else
{
lean_object* v___x_249_; uint8_t v___x_250_; 
v___x_249_ = l_Lean_Expr_appFnCleanup___redArg(v___x_247_);
v___x_250_ = l_Lean_Expr_isApp(v___x_249_);
if (v___x_250_ == 0)
{
lean_dec_ref(v___x_249_);
goto v___jp_233_;
}
else
{
lean_object* v___x_251_; lean_object* v___x_252_; uint8_t v___x_253_; 
v___x_251_ = l_Lean_Expr_appFnCleanup___redArg(v___x_249_);
v___x_252_ = ((lean_object*)(l_Lean_Meta_mkPProd___closed__3));
v___x_253_ = l_Lean_Expr_isConstOf(v___x_251_, v___x_252_);
if (v___x_253_ == 0)
{
lean_object* v___x_254_; uint8_t v___x_255_; 
v___x_254_ = ((lean_object*)(l_Lean_Meta_mkPProd___closed__1));
v___x_255_ = l_Lean_Expr_isConstOf(v___x_251_, v___x_254_);
lean_dec_ref(v___x_251_);
if (v___x_255_ == 0)
{
goto v___jp_233_;
}
else
{
lean_object* v___x_256_; lean_object* v___x_257_; 
lean_dec_ref(v_t_231_);
v___x_256_ = lean_unsigned_to_nat(1u);
v___x_257_ = l_Lean_Expr_proj___override(v___x_254_, v___x_256_, v_e_232_);
return v___x_257_;
}
}
else
{
lean_object* v___x_258_; lean_object* v___x_259_; 
lean_dec_ref(v___x_251_);
lean_dec_ref(v_t_231_);
v___x_258_ = lean_unsigned_to_nat(1u);
v___x_259_ = l_Lean_Expr_proj___override(v___x_252_, v___x_258_, v_e_232_);
return v___x_259_;
}
}
}
v___jp_233_:
{
lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_234_ = ((lean_object*)(l_Lean_Meta_mkPProdFst___closed__0));
v___x_235_ = ((lean_object*)(l_Lean_Meta_mkPProdSnd___closed__0));
v___x_236_ = lean_unsigned_to_nat(77u);
v___x_237_ = lean_unsigned_to_nat(9u);
v___x_238_ = ((lean_object*)(l_Lean_Meta_mkPProdSnd___closed__1));
v___x_239_ = lean_expr_dbg_to_string(v_e_232_);
lean_dec_ref(v_e_232_);
v___x_240_ = lean_string_append(v___x_238_, v___x_239_);
lean_dec_ref(v___x_239_);
v___x_241_ = ((lean_object*)(l_Lean_Meta_mkPProdFst___closed__3));
v___x_242_ = lean_string_append(v___x_240_, v___x_241_);
v___x_243_ = lean_expr_dbg_to_string(v_t_231_);
lean_dec_ref(v_t_231_);
v___x_244_ = lean_string_append(v___x_242_, v___x_243_);
lean_dec_ref(v___x_243_);
v___x_245_ = l_mkPanicMessageWithDecl(v___x_234_, v___x_235_, v___x_236_, v___x_237_, v___x_244_);
lean_dec_ref(v___x_244_);
v___x_246_ = l_panic___at___00Lean_Meta_mkPProdFst_spec__0(v___x_245_);
return v___x_246_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPProdSndM(lean_object* v_e_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_, lean_object* v_a_264_){
_start:
{
lean_object* v___x_266_; 
lean_inc(v_a_264_);
lean_inc_ref(v_a_263_);
lean_inc(v_a_262_);
lean_inc_ref(v_a_261_);
lean_inc_ref(v_e_260_);
v___x_266_ = lean_infer_type(v_e_260_, v_a_261_, v_a_262_, v_a_263_, v_a_264_);
if (lean_obj_tag(v___x_266_) == 0)
{
lean_object* v_a_267_; lean_object* v___x_268_; 
v_a_267_ = lean_ctor_get(v___x_266_, 0);
lean_inc(v_a_267_);
lean_dec_ref_known(v___x_266_, 1);
lean_inc(v_a_264_);
lean_inc_ref(v_a_263_);
lean_inc(v_a_262_);
lean_inc_ref(v_a_261_);
v___x_268_ = lean_whnf(v_a_267_, v_a_261_, v_a_262_, v_a_263_, v_a_264_);
if (lean_obj_tag(v___x_268_) == 0)
{
lean_object* v_a_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_277_; 
v_a_269_ = lean_ctor_get(v___x_268_, 0);
v_isSharedCheck_277_ = !lean_is_exclusive(v___x_268_);
if (v_isSharedCheck_277_ == 0)
{
v___x_271_ = v___x_268_;
v_isShared_272_ = v_isSharedCheck_277_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_a_269_);
lean_dec(v___x_268_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_277_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_273_; lean_object* v___x_275_; 
v___x_273_ = l_Lean_Meta_mkPProdSnd(v_a_269_, v_e_260_);
if (v_isShared_272_ == 0)
{
lean_ctor_set(v___x_271_, 0, v___x_273_);
v___x_275_ = v___x_271_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v___x_273_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
return v___x_275_;
}
}
}
else
{
lean_dec_ref(v_e_260_);
return v___x_268_;
}
}
else
{
lean_dec_ref(v_e_260_);
return v___x_266_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPProdSndM___boxed(lean_object* v_e_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_Lean_Meta_mkPProdSndM(v_e_278_, v_a_279_, v_a_280_, v_a_281_, v_a_282_);
lean_dec(v_a_282_);
lean_dec_ref(v_a_281_);
lean_dec(v_a_280_);
lean_dec_ref(v_a_279_);
return v_res_284_;
}
}
static lean_object* _init_l_Lean_Meta_PProdN_genMk___redArg___closed__0(void){
_start:
{
lean_object* v___x_285_; 
v___x_285_ = l_instMonadEIO___redArg();
return v___x_285_;
}
}
static lean_object* _init_l_Lean_Meta_PProdN_genMk___redArg___closed__1(void){
_start:
{
lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_286_ = lean_obj_once(&l_Lean_Meta_PProdN_genMk___redArg___closed__0, &l_Lean_Meta_PProdN_genMk___redArg___closed__0_once, _init_l_Lean_Meta_PProdN_genMk___redArg___closed__0);
v___x_287_ = l_StateRefT_x27_instMonad___redArg(v___x_286_);
return v___x_287_;
}
}
static lean_object* _init_l_Lean_Meta_PProdN_genMk___redArg___closed__9(void){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_295_ = ((lean_object*)(l_Lean_Meta_PProdN_genMk___redArg___closed__8));
v___x_296_ = lean_unsigned_to_nat(2u);
v___x_297_ = lean_unsigned_to_nat(90u);
v___x_298_ = ((lean_object*)(l_Lean_Meta_PProdN_genMk___redArg___closed__7));
v___x_299_ = ((lean_object*)(l_Lean_Meta_mkPProdFst___closed__0));
v___x_300_ = l_mkPanicMessageWithDecl(v___x_299_, v___x_298_, v___x_297_, v___x_296_, v___x_295_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_genMk___redArg(lean_object* v_inst_301_, lean_object* v_mk_302_, lean_object* v_xs_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_){
_start:
{
lean_object* v___x_309_; lean_object* v_toApplicative_310_; lean_object* v_toFunctor_311_; lean_object* v_toSeq_312_; lean_object* v_toSeqLeft_313_; lean_object* v_toSeqRight_314_; lean_object* v___f_315_; lean_object* v___f_316_; lean_object* v___f_317_; lean_object* v___f_318_; lean_object* v___x_319_; lean_object* v___f_320_; lean_object* v___f_321_; lean_object* v___f_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v_toApplicative_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_371_; 
v___x_309_ = lean_obj_once(&l_Lean_Meta_PProdN_genMk___redArg___closed__1, &l_Lean_Meta_PProdN_genMk___redArg___closed__1_once, _init_l_Lean_Meta_PProdN_genMk___redArg___closed__1);
v_toApplicative_310_ = lean_ctor_get(v___x_309_, 0);
v_toFunctor_311_ = lean_ctor_get(v_toApplicative_310_, 0);
v_toSeq_312_ = lean_ctor_get(v_toApplicative_310_, 2);
v_toSeqLeft_313_ = lean_ctor_get(v_toApplicative_310_, 3);
v_toSeqRight_314_ = lean_ctor_get(v_toApplicative_310_, 4);
v___f_315_ = ((lean_object*)(l_Lean_Meta_PProdN_genMk___redArg___closed__2));
v___f_316_ = ((lean_object*)(l_Lean_Meta_PProdN_genMk___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_311_, 2);
v___f_317_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_317_, 0, v_toFunctor_311_);
v___f_318_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_318_, 0, v_toFunctor_311_);
v___x_319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_319_, 0, v___f_317_);
lean_ctor_set(v___x_319_, 1, v___f_318_);
lean_inc(v_toSeqRight_314_);
v___f_320_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_320_, 0, v_toSeqRight_314_);
lean_inc(v_toSeqLeft_313_);
v___f_321_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_321_, 0, v_toSeqLeft_313_);
lean_inc(v_toSeq_312_);
v___f_322_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_322_, 0, v_toSeq_312_);
v___x_323_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_323_, 0, v___x_319_);
lean_ctor_set(v___x_323_, 1, v___f_315_);
lean_ctor_set(v___x_323_, 2, v___f_322_);
lean_ctor_set(v___x_323_, 3, v___f_321_);
lean_ctor_set(v___x_323_, 4, v___f_320_);
v___x_324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_324_, 0, v___x_323_);
lean_ctor_set(v___x_324_, 1, v___f_316_);
v___x_325_ = l_StateRefT_x27_instMonad___redArg(v___x_324_);
v_toApplicative_326_ = lean_ctor_get(v___x_325_, 0);
v_isSharedCheck_371_ = !lean_is_exclusive(v___x_325_);
if (v_isSharedCheck_371_ == 0)
{
lean_object* v_unused_372_; 
v_unused_372_ = lean_ctor_get(v___x_325_, 1);
lean_dec(v_unused_372_);
v___x_328_ = v___x_325_;
v_isShared_329_ = v_isSharedCheck_371_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_toApplicative_326_);
lean_dec(v___x_325_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_371_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v_toFunctor_330_; lean_object* v_toSeq_331_; lean_object* v_toSeqLeft_332_; lean_object* v_toSeqRight_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_369_; 
v_toFunctor_330_ = lean_ctor_get(v_toApplicative_326_, 0);
v_toSeq_331_ = lean_ctor_get(v_toApplicative_326_, 2);
v_toSeqLeft_332_ = lean_ctor_get(v_toApplicative_326_, 3);
v_toSeqRight_333_ = lean_ctor_get(v_toApplicative_326_, 4);
v_isSharedCheck_369_ = !lean_is_exclusive(v_toApplicative_326_);
if (v_isSharedCheck_369_ == 0)
{
lean_object* v_unused_370_; 
v_unused_370_ = lean_ctor_get(v_toApplicative_326_, 1);
lean_dec(v_unused_370_);
v___x_335_ = v_toApplicative_326_;
v_isShared_336_ = v_isSharedCheck_369_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_toSeqRight_333_);
lean_inc(v_toSeqLeft_332_);
lean_inc(v_toSeq_331_);
lean_inc(v_toFunctor_330_);
lean_dec(v_toApplicative_326_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_369_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___f_337_; lean_object* v___f_338_; lean_object* v___f_339_; lean_object* v___f_340_; lean_object* v___x_341_; lean_object* v___f_342_; lean_object* v___f_343_; lean_object* v___f_344_; lean_object* v___x_346_; 
v___f_337_ = ((lean_object*)(l_Lean_Meta_PProdN_genMk___redArg___closed__4));
v___f_338_ = ((lean_object*)(l_Lean_Meta_PProdN_genMk___redArg___closed__5));
lean_inc_ref(v_toFunctor_330_);
v___f_339_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_339_, 0, v_toFunctor_330_);
v___f_340_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_340_, 0, v_toFunctor_330_);
v___x_341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_341_, 0, v___f_339_);
lean_ctor_set(v___x_341_, 1, v___f_340_);
v___f_342_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_342_, 0, v_toSeqRight_333_);
v___f_343_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_343_, 0, v_toSeqLeft_332_);
v___f_344_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_344_, 0, v_toSeq_331_);
if (v_isShared_336_ == 0)
{
lean_ctor_set(v___x_335_, 4, v___f_342_);
lean_ctor_set(v___x_335_, 3, v___f_343_);
lean_ctor_set(v___x_335_, 2, v___f_344_);
lean_ctor_set(v___x_335_, 1, v___f_337_);
lean_ctor_set(v___x_335_, 0, v___x_341_);
v___x_346_ = v___x_335_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v___x_341_);
lean_ctor_set(v_reuseFailAlloc_368_, 1, v___f_337_);
lean_ctor_set(v_reuseFailAlloc_368_, 2, v___f_344_);
lean_ctor_set(v_reuseFailAlloc_368_, 3, v___f_343_);
lean_ctor_set(v_reuseFailAlloc_368_, 4, v___f_342_);
v___x_346_ = v_reuseFailAlloc_368_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
lean_object* v___x_348_; 
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 1, v___f_338_);
lean_ctor_set(v___x_328_, 0, v___x_346_);
v___x_348_ = v___x_328_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v___x_346_);
lean_ctor_set(v_reuseFailAlloc_367_, 1, v___f_338_);
v___x_348_ = v_reuseFailAlloc_367_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
lean_object* v___x_349_; lean_object* v___x_350_; uint8_t v___x_351_; 
v___x_349_ = lean_array_get_size(v_xs_303_);
v___x_350_ = lean_unsigned_to_nat(0u);
v___x_351_ = lean_nat_dec_eq(v___x_349_, v___x_350_);
if (v___x_351_ == 0)
{
lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; uint8_t v___x_357_; 
v___x_352_ = lean_unsigned_to_nat(1u);
v___x_353_ = lean_nat_sub(v___x_349_, v___x_352_);
v___x_354_ = lean_array_get(v_inst_301_, v_xs_303_, v___x_353_);
lean_dec(v___x_353_);
v___x_355_ = lean_array_pop(v_xs_303_);
v___x_356_ = lean_array_get_size(v___x_355_);
v___x_357_ = lean_nat_dec_lt(v___x_350_, v___x_356_);
if (v___x_357_ == 0)
{
lean_object* v___x_358_; 
lean_dec_ref(v___x_355_);
lean_dec_ref(v___x_348_);
lean_dec_ref(v_mk_302_);
v___x_358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_358_, 0, v___x_354_);
return v___x_358_;
}
else
{
size_t v___x_359_; size_t v___x_360_; lean_object* v___x_271__overap_361_; lean_object* v___x_362_; 
v___x_359_ = lean_usize_of_nat(v___x_356_);
v___x_360_ = ((size_t)0ULL);
v___x_271__overap_361_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_348_, v_mk_302_, v___x_355_, v___x_359_, v___x_360_, v___x_354_);
lean_inc(v_a_307_);
lean_inc_ref(v_a_306_);
lean_inc(v_a_305_);
lean_inc_ref(v_a_304_);
v___x_362_ = lean_apply_5(v___x_271__overap_361_, v_a_304_, v_a_305_, v_a_306_, v_a_307_, lean_box(0));
return v___x_362_;
}
}
else
{
lean_object* v___f_363_; lean_object* v___x_364_; lean_object* v___x_316__overap_365_; lean_object* v___x_366_; 
lean_dec_ref(v___x_348_);
lean_dec_ref(v_xs_303_);
lean_dec_ref(v_mk_302_);
v___f_363_ = ((lean_object*)(l_Lean_Meta_PProdN_genMk___redArg___closed__6));
v___x_364_ = lean_obj_once(&l_Lean_Meta_PProdN_genMk___redArg___closed__9, &l_Lean_Meta_PProdN_genMk___redArg___closed__9_once, _init_l_Lean_Meta_PProdN_genMk___redArg___closed__9);
v___x_316__overap_365_ = l_panic___redArg(v___f_363_, v___x_364_);
lean_inc(v_a_307_);
lean_inc_ref(v_a_306_);
lean_inc(v_a_305_);
lean_inc_ref(v_a_304_);
v___x_366_ = lean_apply_5(v___x_316__overap_365_, v_a_304_, v_a_305_, v_a_306_, v_a_307_, lean_box(0));
return v___x_366_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_genMk___redArg___boxed(lean_object* v_inst_373_, lean_object* v_mk_374_, lean_object* v_xs_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Lean_Meta_PProdN_genMk___redArg(v_inst_373_, v_mk_374_, v_xs_375_, v_a_376_, v_a_377_, v_a_378_, v_a_379_);
lean_dec(v_a_379_);
lean_dec_ref(v_a_378_);
lean_dec(v_a_377_);
lean_dec_ref(v_a_376_);
lean_dec(v_inst_373_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_genMk(lean_object* v_00_u03b1_382_, lean_object* v_inst_383_, lean_object* v_mk_384_, lean_object* v_xs_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_){
_start:
{
lean_object* v___x_391_; 
v___x_391_ = l_Lean_Meta_PProdN_genMk___redArg(v_inst_383_, v_mk_384_, v_xs_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_);
return v___x_391_;
}
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
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_pack(lean_object* v_lvl_412_, lean_object* v_xs_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_pack___boxed(lean_object* v_lvl_433_, lean_object* v_xs_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_Lean_Meta_PProdN_pack(v_lvl_433_, v_xs_434_, v_a_435_, v_a_436_, v_a_437_, v_a_438_);
lean_dec(v_a_438_);
lean_dec_ref(v_a_437_);
lean_dec(v_a_436_);
lean_dec_ref(v_a_435_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_unpack_go___redArg(lean_object* v_e_441_, lean_object* v_remaining_442_, lean_object* v_acc_443_){
_start:
{
lean_object* v___x_448_; uint8_t v___x_449_; 
v___x_448_ = lean_unsigned_to_nat(0u);
v___x_449_ = lean_nat_dec_eq(v_remaining_442_, v___x_448_);
if (v___x_449_ == 0)
{
if (lean_obj_tag(v_e_441_) == 5)
{
lean_object* v_fn_450_; 
v_fn_450_ = lean_ctor_get(v_e_441_, 0);
if (lean_obj_tag(v_fn_450_) == 5)
{
lean_object* v_fn_451_; 
v_fn_451_ = lean_ctor_get(v_fn_450_, 0);
if (lean_obj_tag(v_fn_451_) == 4)
{
lean_object* v_declName_452_; 
v_declName_452_ = lean_ctor_get(v_fn_451_, 0);
if (lean_obj_tag(v_declName_452_) == 1)
{
lean_object* v_pre_453_; 
v_pre_453_ = lean_ctor_get(v_declName_452_, 0);
if (lean_obj_tag(v_pre_453_) == 0)
{
lean_object* v_arg_454_; lean_object* v_arg_455_; lean_object* v_str_456_; lean_object* v___x_457_; uint8_t v___x_458_; 
v_arg_454_ = lean_ctor_get(v_e_441_, 1);
v_arg_455_ = lean_ctor_get(v_fn_450_, 1);
v_str_456_ = lean_ctor_get(v_declName_452_, 1);
v___x_457_ = ((lean_object*)(l_Lean_Meta_mkPProd___closed__0));
v___x_458_ = lean_string_dec_eq(v_str_456_, v___x_457_);
if (v___x_458_ == 0)
{
lean_dec(v_remaining_442_);
goto v___jp_445_;
}
else
{
lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
lean_inc_ref(v_arg_455_);
lean_inc_ref(v_arg_454_);
lean_dec_ref_known(v_e_441_, 2);
v___x_459_ = lean_unsigned_to_nat(1u);
v___x_460_ = lean_nat_sub(v_remaining_442_, v___x_459_);
lean_dec(v_remaining_442_);
v___x_461_ = lean_array_push(v_acc_443_, v_arg_455_);
v_e_441_ = v_arg_454_;
v_remaining_442_ = v___x_460_;
v_acc_443_ = v___x_461_;
goto _start;
}
}
else
{
lean_dec(v_remaining_442_);
goto v___jp_445_;
}
}
else
{
lean_dec(v_remaining_442_);
goto v___jp_445_;
}
}
else
{
lean_dec(v_remaining_442_);
goto v___jp_445_;
}
}
else
{
lean_dec(v_remaining_442_);
goto v___jp_445_;
}
}
else
{
lean_dec(v_remaining_442_);
goto v___jp_445_;
}
}
else
{
lean_object* v___x_463_; 
lean_dec(v_remaining_442_);
lean_dec_ref(v_e_441_);
v___x_463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_463_, 0, v_acc_443_);
return v___x_463_;
}
v___jp_445_:
{
lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_446_ = lean_array_push(v_acc_443_, v_e_441_);
v___x_447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_447_, 0, v___x_446_);
return v___x_447_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_unpack_go___redArg___boxed(lean_object* v_e_464_, lean_object* v_remaining_465_, lean_object* v_acc_466_, lean_object* v_a_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_unpack_go___redArg(v_e_464_, v_remaining_465_, v_acc_466_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_unpack_go(lean_object* v_e_469_, lean_object* v_remaining_470_, lean_object* v_acc_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_){
_start:
{
lean_object* v___x_477_; 
v___x_477_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_unpack_go___redArg(v_e_469_, v_remaining_470_, v_acc_471_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_unpack_go___boxed(lean_object* v_e_478_, lean_object* v_remaining_479_, lean_object* v_acc_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_unpack_go(v_e_478_, v_remaining_479_, v_acc_480_, v_a_481_, v_a_482_, v_a_483_, v_a_484_);
lean_dec(v_a_484_);
lean_dec_ref(v_a_483_);
lean_dec(v_a_482_);
lean_dec_ref(v_a_481_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_unpack___redArg(lean_object* v_e_489_, lean_object* v_n_490_){
_start:
{
if (lean_obj_tag(v_e_489_) == 4)
{
lean_object* v_declName_498_; 
v_declName_498_ = lean_ctor_get(v_e_489_, 0);
if (lean_obj_tag(v_declName_498_) == 1)
{
lean_object* v_pre_499_; 
v_pre_499_ = lean_ctor_get(v_declName_498_, 0);
if (lean_obj_tag(v_pre_499_) == 0)
{
lean_object* v_str_500_; lean_object* v___x_501_; uint8_t v___x_502_; 
v_str_500_ = lean_ctor_get(v_declName_498_, 1);
v___x_501_ = ((lean_object*)(l_Lean_Meta_PProdN_pack___closed__3));
v___x_502_ = lean_string_dec_eq(v_str_500_, v___x_501_);
if (v___x_502_ == 0)
{
lean_object* v___x_503_; uint8_t v___x_504_; 
v___x_503_ = ((lean_object*)(l_Lean_Meta_PProdN_pack___closed__1));
v___x_504_ = lean_string_dec_eq(v_str_500_, v___x_503_);
if (v___x_504_ == 0)
{
goto v___jp_492_;
}
else
{
lean_dec_ref_known(v_e_489_, 2);
lean_dec(v_n_490_);
goto v___jp_495_;
}
}
else
{
lean_dec_ref_known(v_e_489_, 2);
lean_dec(v_n_490_);
goto v___jp_495_;
}
}
else
{
goto v___jp_492_;
}
}
else
{
goto v___jp_492_;
}
}
else
{
goto v___jp_492_;
}
v___jp_492_:
{
lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_493_ = ((lean_object*)(l_Lean_Meta_PProdN_unpack___redArg___closed__0));
v___x_494_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_unpack_go___redArg(v_e_489_, v_n_490_, v___x_493_);
return v___x_494_;
}
v___jp_495_:
{
lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_496_ = ((lean_object*)(l_Lean_Meta_PProdN_unpack___redArg___closed__0));
v___x_497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_497_, 0, v___x_496_);
return v___x_497_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_unpack___redArg___boxed(lean_object* v_e_505_, lean_object* v_n_506_, lean_object* v_a_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l_Lean_Meta_PProdN_unpack___redArg(v_e_505_, v_n_506_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_unpack(lean_object* v_e_509_, lean_object* v_n_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_){
_start:
{
lean_object* v___x_516_; 
v___x_516_ = l_Lean_Meta_PProdN_unpack___redArg(v_e_509_, v_n_510_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_unpack___boxed(lean_object* v_e_517_, lean_object* v_n_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_Lean_Meta_PProdN_unpack(v_e_517_, v_n_518_, v_a_519_, v_a_520_, v_a_521_, v_a_522_);
lean_dec(v_a_522_);
lean_dec_ref(v_a_521_);
lean_dec(v_a_520_);
lean_dec_ref(v_a_519_);
return v_res_524_;
}
}
static lean_object* _init_l_Lean_Meta_PProdN_mk___closed__4(void){
_start:
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_533_ = lean_box(0);
v___x_534_ = ((lean_object*)(l_Lean_Meta_PProdN_mk___closed__3));
v___x_535_ = l_Lean_Expr_const___override(v___x_534_, v___x_533_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_mk(lean_object* v_lvl_536_, lean_object* v_xs_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_){
_start:
{
lean_object* v___x_543_; lean_object* v___x_544_; uint8_t v___x_545_; 
v___x_543_ = lean_array_get_size(v_xs_537_);
v___x_544_ = lean_unsigned_to_nat(0u);
v___x_545_ = lean_nat_dec_eq(v___x_543_, v___x_544_);
if (v___x_545_ == 0)
{
lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
lean_dec(v_lvl_536_);
v___x_546_ = l_Lean_instInhabitedExpr;
v___x_547_ = ((lean_object*)(l_Lean_Meta_PProdN_mk___closed__0));
v___x_548_ = l_Lean_Meta_PProdN_genMk___redArg(v___x_546_, v___x_547_, v_xs_537_, v_a_538_, v_a_539_, v_a_540_, v_a_541_);
return v___x_548_;
}
else
{
uint8_t v___x_549_; 
lean_dec_ref(v_xs_537_);
v___x_549_ = l_Lean_Level_isAlwaysZero(v_lvl_536_);
if (v___x_549_ == 0)
{
lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_550_ = ((lean_object*)(l_Lean_Meta_PProdN_mk___closed__2));
v___x_551_ = lean_box(0);
v___x_552_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_552_, 0, v_lvl_536_);
lean_ctor_set(v___x_552_, 1, v___x_551_);
v___x_553_ = l_Lean_Expr_const___override(v___x_550_, v___x_552_);
v___x_554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_554_, 0, v___x_553_);
return v___x_554_;
}
else
{
lean_object* v___x_555_; lean_object* v___x_556_; 
lean_dec(v_lvl_536_);
v___x_555_ = lean_obj_once(&l_Lean_Meta_PProdN_mk___closed__4, &l_Lean_Meta_PProdN_mk___closed__4_once, _init_l_Lean_Meta_PProdN_mk___closed__4);
v___x_556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_556_, 0, v___x_555_);
return v___x_556_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_mk___boxed(lean_object* v_lvl_557_, lean_object* v_xs_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l_Lean_Meta_PProdN_mk(v_lvl_557_, v_xs_558_, v_a_559_, v_a_560_, v_a_561_, v_a_562_);
lean_dec(v_a_562_);
lean_dec_ref(v_a_561_);
lean_dec(v_a_560_);
lean_dec_ref(v_a_559_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_proj_spec__0___redArg(lean_object* v_upperBound_565_, lean_object* v_a_566_, lean_object* v_b_567_){
_start:
{
uint8_t v___x_568_; 
v___x_568_ = lean_nat_dec_lt(v_a_566_, v_upperBound_565_);
if (v___x_568_ == 0)
{
lean_dec(v_a_566_);
return v_b_567_;
}
else
{
lean_object* v_fst_569_; lean_object* v_snd_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_582_; 
v_fst_569_ = lean_ctor_get(v_b_567_, 0);
v_snd_570_ = lean_ctor_get(v_b_567_, 1);
v_isSharedCheck_582_ = !lean_is_exclusive(v_b_567_);
if (v_isSharedCheck_582_ == 0)
{
v___x_572_ = v_b_567_;
v_isShared_573_ = v_isSharedCheck_582_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_snd_570_);
lean_inc(v_fst_569_);
lean_dec(v_b_567_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_582_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_577_; 
lean_inc(v_fst_569_);
v___x_574_ = l_Lean_Meta_mkPProdSnd(v_fst_569_, v_snd_570_);
v___x_575_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_mkTypeSnd(v_fst_569_);
if (v_isShared_573_ == 0)
{
lean_ctor_set(v___x_572_, 1, v___x_574_);
lean_ctor_set(v___x_572_, 0, v___x_575_);
v___x_577_ = v___x_572_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v___x_575_);
lean_ctor_set(v_reuseFailAlloc_581_, 1, v___x_574_);
v___x_577_ = v_reuseFailAlloc_581_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_578_ = lean_unsigned_to_nat(1u);
v___x_579_ = lean_nat_add(v_a_566_, v___x_578_);
lean_dec(v_a_566_);
v_a_566_ = v___x_579_;
v_b_567_ = v___x_577_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_proj_spec__0___redArg___boxed(lean_object* v_upperBound_583_, lean_object* v_a_584_, lean_object* v_b_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_proj_spec__0___redArg(v_upperBound_583_, v_a_584_, v_b_585_);
lean_dec(v_upperBound_583_);
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_proj(lean_object* v_n_587_, lean_object* v_i_588_, lean_object* v_t_589_, lean_object* v_e_590_){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v_fst_594_; lean_object* v_snd_595_; lean_object* v___x_596_; lean_object* v___x_597_; uint8_t v___x_598_; 
v___x_591_ = lean_unsigned_to_nat(0u);
v___x_592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_592_, 0, v_t_589_);
lean_ctor_set(v___x_592_, 1, v_e_590_);
v___x_593_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_proj_spec__0___redArg(v_i_588_, v___x_591_, v___x_592_);
v_fst_594_ = lean_ctor_get(v___x_593_, 0);
lean_inc(v_fst_594_);
v_snd_595_ = lean_ctor_get(v___x_593_, 1);
lean_inc(v_snd_595_);
lean_dec_ref(v___x_593_);
v___x_596_ = lean_unsigned_to_nat(1u);
v___x_597_ = lean_nat_add(v_i_588_, v___x_596_);
v___x_598_ = lean_nat_dec_lt(v___x_597_, v_n_587_);
lean_dec(v___x_597_);
if (v___x_598_ == 0)
{
lean_dec(v_fst_594_);
return v_snd_595_;
}
else
{
lean_object* v___x_599_; 
v___x_599_ = l_Lean_Meta_mkPProdFst(v_fst_594_, v_snd_595_);
return v___x_599_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_proj___boxed(lean_object* v_n_600_, lean_object* v_i_601_, lean_object* v_t_602_, lean_object* v_e_603_){
_start:
{
lean_object* v_res_604_; 
v_res_604_ = l_Lean_Meta_PProdN_proj(v_n_600_, v_i_601_, v_t_602_, v_e_603_);
lean_dec(v_i_601_);
lean_dec(v_n_600_);
return v_res_604_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_proj_spec__0(lean_object* v_upperBound_605_, lean_object* v_inst_606_, lean_object* v_R_607_, lean_object* v_a_608_, lean_object* v_b_609_, lean_object* v_c_610_){
_start:
{
lean_object* v___x_611_; 
v___x_611_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_proj_spec__0___redArg(v_upperBound_605_, v_a_608_, v_b_609_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_proj_spec__0___boxed(lean_object* v_upperBound_612_, lean_object* v_inst_613_, lean_object* v_R_614_, lean_object* v_a_615_, lean_object* v_b_616_, lean_object* v_c_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_proj_spec__0(v_upperBound_612_, v_inst_613_, v_R_614_, v_a_615_, v_b_616_, v_c_617_);
lean_dec(v_upperBound_612_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_projs___lam__0(lean_object* v_n_619_, lean_object* v_t_620_, lean_object* v_e_621_, lean_object* v_i_622_){
_start:
{
lean_object* v___x_623_; 
v___x_623_ = l_Lean_Meta_PProdN_proj(v_n_619_, v_i_622_, v_t_620_, v_e_621_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_projs___lam__0___boxed(lean_object* v_n_624_, lean_object* v_t_625_, lean_object* v_e_626_, lean_object* v_i_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l_Lean_Meta_PProdN_projs___lam__0(v_n_624_, v_t_625_, v_e_626_, v_i_627_);
lean_dec(v_i_627_);
lean_dec(v_n_624_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_projs(lean_object* v_n_629_, lean_object* v_t_630_, lean_object* v_e_631_){
_start:
{
lean_object* v___f_632_; lean_object* v___x_633_; 
lean_inc(v_n_629_);
v___f_632_ = lean_alloc_closure((void*)(l_Lean_Meta_PProdN_projs___lam__0___boxed), 4, 3);
lean_closure_set(v___f_632_, 0, v_n_629_);
lean_closure_set(v___f_632_, 1, v_t_630_);
lean_closure_set(v___f_632_, 2, v_e_631_);
v___x_633_ = l_Array_ofFn___redArg(v_n_629_, v___f_632_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_projM_spec__0___redArg(lean_object* v_upperBound_634_, lean_object* v_a_635_, lean_object* v_b_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_){
_start:
{
uint8_t v___x_642_; 
v___x_642_ = lean_nat_dec_lt(v_a_635_, v_upperBound_634_);
if (v___x_642_ == 0)
{
lean_object* v___x_643_; 
lean_dec(v_a_635_);
v___x_643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_643_, 0, v_b_636_);
return v___x_643_;
}
else
{
lean_object* v___x_644_; 
v___x_644_ = l_Lean_Meta_mkPProdSndM(v_b_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_);
if (lean_obj_tag(v___x_644_) == 0)
{
lean_object* v_a_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
v_a_645_ = lean_ctor_get(v___x_644_, 0);
lean_inc(v_a_645_);
lean_dec_ref_known(v___x_644_, 1);
v___x_646_ = lean_unsigned_to_nat(1u);
v___x_647_ = lean_nat_add(v_a_635_, v___x_646_);
lean_dec(v_a_635_);
v_a_635_ = v___x_647_;
v_b_636_ = v_a_645_;
goto _start;
}
else
{
lean_dec(v_a_635_);
return v___x_644_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_projM_spec__0___redArg___boxed(lean_object* v_upperBound_649_, lean_object* v_a_650_, lean_object* v_b_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_projM_spec__0___redArg(v_upperBound_649_, v_a_650_, v_b_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_);
lean_dec(v___y_655_);
lean_dec_ref(v___y_654_);
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
lean_dec(v_upperBound_649_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_projM(lean_object* v_n_658_, lean_object* v_i_659_, lean_object* v_e_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_){
_start:
{
lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_666_ = lean_unsigned_to_nat(0u);
v___x_667_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_projM_spec__0___redArg(v_i_659_, v___x_666_, v_e_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_);
if (lean_obj_tag(v___x_667_) == 0)
{
lean_object* v_a_668_; lean_object* v___x_669_; lean_object* v___x_670_; uint8_t v___x_671_; 
v_a_668_ = lean_ctor_get(v___x_667_, 0);
v___x_669_ = lean_unsigned_to_nat(1u);
v___x_670_ = lean_nat_add(v_i_659_, v___x_669_);
v___x_671_ = lean_nat_dec_lt(v___x_670_, v_n_658_);
lean_dec(v___x_670_);
if (v___x_671_ == 0)
{
return v___x_667_;
}
else
{
lean_object* v___x_672_; 
lean_inc(v_a_668_);
lean_dec_ref_known(v___x_667_, 1);
v___x_672_ = l_Lean_Meta_mkPProdFstM(v_a_668_, v_a_661_, v_a_662_, v_a_663_, v_a_664_);
return v___x_672_;
}
}
else
{
return v___x_667_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_projM___boxed(lean_object* v_n_673_, lean_object* v_i_674_, lean_object* v_e_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Lean_Meta_PProdN_projM(v_n_673_, v_i_674_, v_e_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_);
lean_dec(v_a_679_);
lean_dec_ref(v_a_678_);
lean_dec(v_a_677_);
lean_dec_ref(v_a_676_);
lean_dec(v_i_674_);
lean_dec(v_n_673_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_projM_spec__0(lean_object* v_upperBound_682_, lean_object* v_inst_683_, lean_object* v_R_684_, lean_object* v_a_685_, lean_object* v_b_686_, lean_object* v_c_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_){
_start:
{
lean_object* v___x_693_; 
v___x_693_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_projM_spec__0___redArg(v_upperBound_682_, v_a_685_, v_b_686_, v___y_688_, v___y_689_, v___y_690_, v___y_691_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_projM_spec__0___boxed(lean_object* v_upperBound_694_, lean_object* v_inst_695_, lean_object* v_R_696_, lean_object* v_a_697_, lean_object* v_b_698_, lean_object* v_c_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_){
_start:
{
lean_object* v_res_705_; 
v_res_705_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_projM_spec__0(v_upperBound_694_, v_inst_695_, v_R_696_, v_a_697_, v_b_698_, v_c_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
lean_dec(v___y_701_);
lean_dec_ref(v___y_700_);
lean_dec(v_upperBound_694_);
return v_res_705_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_PProdN_packLambdas_spec__0(lean_object* v_msg_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_){
_start:
{
lean_object* v___f_712_; lean_object* v___x_336__overap_713_; lean_object* v___x_714_; 
v___f_712_ = ((lean_object*)(l_Lean_Meta_PProdN_genMk___redArg___closed__6));
v___x_336__overap_713_ = lean_panic_fn_borrowed(v___f_712_, v_msg_706_);
lean_inc(v___y_710_);
lean_inc_ref(v___y_709_);
lean_inc(v___y_708_);
lean_inc_ref(v___y_707_);
v___x_714_ = lean_apply_5(v___x_336__overap_713_, v___y_707_, v___y_708_, v___y_709_, v___y_710_, lean_box(0));
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_PProdN_packLambdas_spec__0___boxed(lean_object* v_msg_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l_panic___at___00Lean_Meta_PProdN_packLambdas_spec__0(v_msg_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___redArg___lam__0(lean_object* v_k_722_, lean_object* v_b_723_, lean_object* v_c_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_){
_start:
{
lean_object* v___x_730_; 
lean_inc(v___y_728_);
lean_inc_ref(v___y_727_);
lean_inc(v___y_726_);
lean_inc_ref(v___y_725_);
v___x_730_ = lean_apply_7(v_k_722_, v_b_723_, v_c_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, lean_box(0));
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___redArg___lam__0___boxed(lean_object* v_k_731_, lean_object* v_b_732_, lean_object* v_c_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___redArg___lam__0(v_k_731_, v_b_732_, v_c_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___redArg(lean_object* v_type_740_, lean_object* v_k_741_, uint8_t v_cleanupAnnotations_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_){
_start:
{
lean_object* v___f_748_; uint8_t v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
v___f_748_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_748_, 0, v_k_741_);
v___x_749_ = 0;
v___x_750_ = lean_box(0);
v___x_751_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_749_, v___x_750_, v_type_740_, v___f_748_, v_cleanupAnnotations_742_, v___x_749_, v___y_743_, v___y_744_, v___y_745_, v___y_746_);
if (lean_obj_tag(v___x_751_) == 0)
{
lean_object* v_a_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_759_; 
v_a_752_ = lean_ctor_get(v___x_751_, 0);
v_isSharedCheck_759_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_759_ == 0)
{
v___x_754_ = v___x_751_;
v_isShared_755_ = v_isSharedCheck_759_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_a_752_);
lean_dec(v___x_751_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_759_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v___x_757_; 
if (v_isShared_755_ == 0)
{
v___x_757_ = v___x_754_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v_a_752_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
return v___x_757_;
}
}
}
else
{
lean_object* v_a_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_767_; 
v_a_760_ = lean_ctor_get(v___x_751_, 0);
v_isSharedCheck_767_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_767_ == 0)
{
v___x_762_ = v___x_751_;
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_a_760_);
lean_dec(v___x_751_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v___x_765_; 
if (v_isShared_763_ == 0)
{
v___x_765_ = v___x_762_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v_a_760_);
v___x_765_ = v_reuseFailAlloc_766_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
return v___x_765_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___redArg___boxed(lean_object* v_type_768_, lean_object* v_k_769_, lean_object* v_cleanupAnnotations_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_776_; lean_object* v_res_777_; 
v_cleanupAnnotations_boxed_776_ = lean_unbox(v_cleanupAnnotations_770_);
v_res_777_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___redArg(v_type_768_, v_k_769_, v_cleanupAnnotations_boxed_776_, v___y_771_, v___y_772_, v___y_773_, v___y_774_);
lean_dec(v___y_774_);
lean_dec_ref(v___y_773_);
lean_dec(v___y_772_);
lean_dec_ref(v___y_771_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2(lean_object* v_00_u03b1_778_, lean_object* v_type_779_, lean_object* v_k_780_, uint8_t v_cleanupAnnotations_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_){
_start:
{
lean_object* v___x_787_; 
v___x_787_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___redArg(v_type_779_, v_k_780_, v_cleanupAnnotations_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___boxed(lean_object* v_00_u03b1_788_, lean_object* v_type_789_, lean_object* v_k_790_, lean_object* v_cleanupAnnotations_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_797_; lean_object* v_res_798_; 
v_cleanupAnnotations_boxed_797_ = lean_unbox(v_cleanupAnnotations_791_);
v_res_798_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2(v_00_u03b1_788_, v_type_789_, v_k_790_, v_cleanupAnnotations_boxed_797_, v___y_792_, v___y_793_, v___y_794_, v___y_795_);
lean_dec(v___y_795_);
lean_dec_ref(v___y_794_);
lean_dec(v___y_793_);
lean_dec_ref(v___y_792_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_PProdN_packLambdas_spec__1(lean_object* v_xs_799_, size_t v_sz_800_, size_t v_i_801_, lean_object* v_bs_802_){
_start:
{
uint8_t v___x_803_; 
v___x_803_ = lean_usize_dec_lt(v_i_801_, v_sz_800_);
if (v___x_803_ == 0)
{
lean_dec_ref(v_xs_799_);
return v_bs_802_;
}
else
{
lean_object* v_v_804_; lean_object* v___x_805_; lean_object* v_bs_x27_806_; lean_object* v___x_807_; size_t v___x_808_; size_t v___x_809_; lean_object* v___x_810_; 
v_v_804_ = lean_array_uget(v_bs_802_, v_i_801_);
v___x_805_ = lean_unsigned_to_nat(0u);
v_bs_x27_806_ = lean_array_uset(v_bs_802_, v_i_801_, v___x_805_);
lean_inc_ref(v_xs_799_);
v___x_807_ = l_Lean_Expr_beta(v_v_804_, v_xs_799_);
v___x_808_ = ((size_t)1ULL);
v___x_809_ = lean_usize_add(v_i_801_, v___x_808_);
v___x_810_ = lean_array_uset(v_bs_x27_806_, v_i_801_, v___x_807_);
v_i_801_ = v___x_809_;
v_bs_802_ = v___x_810_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_PProdN_packLambdas_spec__1___boxed(lean_object* v_xs_812_, lean_object* v_sz_813_, lean_object* v_i_814_, lean_object* v_bs_815_){
_start:
{
size_t v_sz_boxed_816_; size_t v_i_boxed_817_; lean_object* v_res_818_; 
v_sz_boxed_816_ = lean_unbox_usize(v_sz_813_);
lean_dec(v_sz_813_);
v_i_boxed_817_ = lean_unbox_usize(v_i_814_);
lean_dec(v_i_814_);
v_res_818_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_PProdN_packLambdas_spec__1(v_xs_812_, v_sz_boxed_816_, v_i_boxed_817_, v_bs_815_);
return v_res_818_;
}
}
static lean_object* _init_l_Lean_Meta_PProdN_packLambdas___lam__0___closed__2(void){
_start:
{
lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_821_ = ((lean_object*)(l_Lean_Meta_PProdN_packLambdas___lam__0___closed__1));
v___x_822_ = lean_unsigned_to_nat(4u);
v___x_823_ = lean_unsigned_to_nat(175u);
v___x_824_ = ((lean_object*)(l_Lean_Meta_PProdN_packLambdas___lam__0___closed__0));
v___x_825_ = ((lean_object*)(l_Lean_Meta_mkPProdFst___closed__0));
v___x_826_ = l_mkPanicMessageWithDecl(v___x_825_, v___x_824_, v___x_823_, v___x_822_, v___x_821_);
return v___x_826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_packLambdas___lam__0(lean_object* v_es_827_, uint8_t v___x_828_, lean_object* v_xs_829_, lean_object* v_sort_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_){
_start:
{
uint8_t v___x_836_; 
v___x_836_ = l_Lean_Expr_isSort(v_sort_830_);
if (v___x_836_ == 0)
{
lean_object* v___x_837_; lean_object* v___x_838_; 
lean_dec_ref(v_xs_829_);
lean_dec_ref(v_es_827_);
v___x_837_ = lean_obj_once(&l_Lean_Meta_PProdN_packLambdas___lam__0___closed__2, &l_Lean_Meta_PProdN_packLambdas___lam__0___closed__2_once, _init_l_Lean_Meta_PProdN_packLambdas___lam__0___closed__2);
v___x_838_ = l_panic___at___00Lean_Meta_PProdN_packLambdas_spec__0(v___x_837_, v___y_831_, v___y_832_, v___y_833_, v___y_834_);
return v___x_838_;
}
else
{
size_t v_sz_839_; size_t v___x_840_; lean_object* v_es_x27_841_; lean_object* v___x_842_; lean_object* v___x_843_; 
v_sz_839_ = lean_array_size(v_es_827_);
v___x_840_ = ((size_t)0ULL);
lean_inc_ref(v_xs_829_);
v_es_x27_841_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_PProdN_packLambdas_spec__1(v_xs_829_, v_sz_839_, v___x_840_, v_es_827_);
v___x_842_ = l_Lean_Expr_sortLevel_x21(v_sort_830_);
v___x_843_ = l_Lean_Meta_PProdN_pack(v___x_842_, v_es_x27_841_, v___y_831_, v___y_832_, v___y_833_, v___y_834_);
if (lean_obj_tag(v___x_843_) == 0)
{
lean_object* v_a_844_; uint8_t v___x_845_; lean_object* v___x_846_; 
v_a_844_ = lean_ctor_get(v___x_843_, 0);
lean_inc(v_a_844_);
lean_dec_ref_known(v___x_843_, 1);
v___x_845_ = 1;
v___x_846_ = l_Lean_Meta_mkLambdaFVars(v_xs_829_, v_a_844_, v___x_828_, v___x_836_, v___x_828_, v___x_836_, v___x_845_, v___y_831_, v___y_832_, v___y_833_, v___y_834_);
lean_dec_ref(v_xs_829_);
return v___x_846_;
}
else
{
lean_dec_ref(v_xs_829_);
return v___x_843_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_packLambdas___lam__0___boxed(lean_object* v_es_847_, lean_object* v___x_848_, lean_object* v_xs_849_, lean_object* v_sort_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_){
_start:
{
uint8_t v___x_936__boxed_856_; lean_object* v_res_857_; 
v___x_936__boxed_856_ = lean_unbox(v___x_848_);
v_res_857_ = l_Lean_Meta_PProdN_packLambdas___lam__0(v_es_847_, v___x_936__boxed_856_, v_xs_849_, v_sort_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_);
lean_dec(v___y_854_);
lean_dec_ref(v___y_853_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
lean_dec_ref(v_sort_850_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_packLambdas(lean_object* v_type_858_, lean_object* v_es_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_){
_start:
{
lean_object* v___x_865_; lean_object* v___x_866_; uint8_t v___x_867_; 
v___x_865_ = lean_array_get_size(v_es_859_);
v___x_866_ = lean_unsigned_to_nat(1u);
v___x_867_ = lean_nat_dec_eq(v___x_865_, v___x_866_);
if (v___x_867_ == 0)
{
lean_object* v___x_868_; lean_object* v___f_869_; lean_object* v___x_870_; 
v___x_868_ = lean_box(v___x_867_);
v___f_869_ = lean_alloc_closure((void*)(l_Lean_Meta_PProdN_packLambdas___lam__0___boxed), 9, 2);
lean_closure_set(v___f_869_, 0, v_es_859_);
lean_closure_set(v___f_869_, 1, v___x_868_);
v___x_870_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___redArg(v_type_858_, v___f_869_, v___x_867_, v_a_860_, v_a_861_, v_a_862_, v_a_863_);
return v___x_870_;
}
else
{
lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; 
lean_dec_ref(v_type_858_);
v___x_871_ = lean_unsigned_to_nat(0u);
v___x_872_ = lean_array_fget(v_es_859_, v___x_871_);
lean_dec_ref(v_es_859_);
v___x_873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_873_, 0, v___x_872_);
return v___x_873_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_packLambdas___boxed(lean_object* v_type_874_, lean_object* v_es_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l_Lean_Meta_PProdN_packLambdas(v_type_874_, v_es_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_);
lean_dec(v_a_879_);
lean_dec_ref(v_a_878_);
lean_dec(v_a_877_);
lean_dec_ref(v_a_876_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_mkLambdas___lam__0(lean_object* v_es_882_, uint8_t v___x_883_, lean_object* v_xs_884_, lean_object* v_body_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_){
_start:
{
lean_object* v___x_891_; 
v___x_891_ = l_Lean_Meta_getLevel(v_body_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_);
if (lean_obj_tag(v___x_891_) == 0)
{
lean_object* v_a_892_; size_t v_sz_893_; size_t v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; 
v_a_892_ = lean_ctor_get(v___x_891_, 0);
lean_inc(v_a_892_);
lean_dec_ref_known(v___x_891_, 1);
v_sz_893_ = lean_array_size(v_es_882_);
v___x_894_ = ((size_t)0ULL);
lean_inc_ref(v_xs_884_);
v___x_895_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_PProdN_packLambdas_spec__1(v_xs_884_, v_sz_893_, v___x_894_, v_es_882_);
v___x_896_ = l_Lean_Meta_PProdN_mk(v_a_892_, v___x_895_, v___y_886_, v___y_887_, v___y_888_, v___y_889_);
if (lean_obj_tag(v___x_896_) == 0)
{
lean_object* v_a_897_; uint8_t v___x_898_; uint8_t v___x_899_; lean_object* v___x_900_; 
v_a_897_ = lean_ctor_get(v___x_896_, 0);
lean_inc(v_a_897_);
lean_dec_ref_known(v___x_896_, 1);
v___x_898_ = 1;
v___x_899_ = 1;
v___x_900_ = l_Lean_Meta_mkLambdaFVars(v_xs_884_, v_a_897_, v___x_883_, v___x_898_, v___x_883_, v___x_898_, v___x_899_, v___y_886_, v___y_887_, v___y_888_, v___y_889_);
lean_dec_ref(v_xs_884_);
return v___x_900_;
}
else
{
lean_dec_ref(v_xs_884_);
return v___x_896_;
}
}
else
{
lean_object* v_a_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_908_; 
lean_dec_ref(v_xs_884_);
lean_dec_ref(v_es_882_);
v_a_901_ = lean_ctor_get(v___x_891_, 0);
v_isSharedCheck_908_ = !lean_is_exclusive(v___x_891_);
if (v_isSharedCheck_908_ == 0)
{
v___x_903_ = v___x_891_;
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_a_901_);
lean_dec(v___x_891_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v___x_906_; 
if (v_isShared_904_ == 0)
{
v___x_906_ = v___x_903_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v_a_901_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
return v___x_906_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_mkLambdas___lam__0___boxed(lean_object* v_es_909_, lean_object* v___x_910_, lean_object* v_xs_911_, lean_object* v_body_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_){
_start:
{
uint8_t v___x_364__boxed_918_; lean_object* v_res_919_; 
v___x_364__boxed_918_ = lean_unbox(v___x_910_);
v_res_919_ = l_Lean_Meta_PProdN_mkLambdas___lam__0(v_es_909_, v___x_364__boxed_918_, v_xs_911_, v_body_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_);
lean_dec(v___y_916_);
lean_dec_ref(v___y_915_);
lean_dec(v___y_914_);
lean_dec_ref(v___y_913_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_mkLambdas(lean_object* v_type_920_, lean_object* v_es_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_){
_start:
{
lean_object* v___x_927_; lean_object* v___x_928_; uint8_t v___x_929_; 
v___x_927_ = lean_array_get_size(v_es_921_);
v___x_928_ = lean_unsigned_to_nat(1u);
v___x_929_ = lean_nat_dec_eq(v___x_927_, v___x_928_);
if (v___x_929_ == 0)
{
lean_object* v___x_930_; lean_object* v___f_931_; lean_object* v___x_932_; 
v___x_930_ = lean_box(v___x_929_);
v___f_931_ = lean_alloc_closure((void*)(l_Lean_Meta_PProdN_mkLambdas___lam__0___boxed), 9, 2);
lean_closure_set(v___f_931_, 0, v_es_921_);
lean_closure_set(v___f_931_, 1, v___x_930_);
v___x_932_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___redArg(v_type_920_, v___f_931_, v___x_929_, v_a_922_, v_a_923_, v_a_924_, v_a_925_);
return v___x_932_;
}
else
{
lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; 
lean_dec_ref(v_type_920_);
v___x_933_ = lean_unsigned_to_nat(0u);
v___x_934_ = lean_array_fget(v_es_921_, v___x_933_);
lean_dec_ref(v_es_921_);
v___x_935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_935_, 0, v___x_934_);
return v___x_935_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_mkLambdas___boxed(lean_object* v_type_936_, lean_object* v_es_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l_Lean_Meta_PProdN_mkLambdas(v_type_936_, v_es_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_);
lean_dec(v_a_941_);
lean_dec_ref(v_a_940_);
lean_dec(v_a_939_);
lean_dec_ref(v_a_938_);
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_stripProjs(lean_object* v_e_944_){
_start:
{
if (lean_obj_tag(v_e_944_) == 11)
{
lean_object* v_typeName_945_; 
v_typeName_945_ = lean_ctor_get(v_e_944_, 0);
if (lean_obj_tag(v_typeName_945_) == 1)
{
lean_object* v_pre_946_; 
v_pre_946_ = lean_ctor_get(v_typeName_945_, 0);
if (lean_obj_tag(v_pre_946_) == 0)
{
lean_object* v_struct_947_; lean_object* v_str_948_; lean_object* v___x_949_; uint8_t v___x_950_; 
v_struct_947_ = lean_ctor_get(v_e_944_, 2);
v_str_948_ = lean_ctor_get(v_typeName_945_, 1);
v___x_949_ = ((lean_object*)(l_Lean_Meta_mkPProd___closed__0));
v___x_950_ = lean_string_dec_eq(v_str_948_, v___x_949_);
if (v___x_950_ == 0)
{
lean_object* v___x_951_; uint8_t v___x_952_; 
v___x_951_ = ((lean_object*)(l_Lean_Meta_mkPProd___closed__2));
v___x_952_ = lean_string_dec_eq(v_str_948_, v___x_951_);
if (v___x_952_ == 0)
{
lean_inc_ref(v_e_944_);
return v_e_944_;
}
else
{
v_e_944_ = v_struct_947_;
goto _start;
}
}
else
{
v_e_944_ = v_struct_947_;
goto _start;
}
}
else
{
lean_inc_ref(v_e_944_);
return v_e_944_;
}
}
else
{
lean_inc_ref(v_e_944_);
return v_e_944_;
}
}
else
{
lean_inc_ref(v_e_944_);
return v_e_944_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_stripProjs___boxed(lean_object* v_e_955_){
_start:
{
lean_object* v_res_956_; 
v_res_956_ = l_Lean_Meta_PProdN_stripProjs(v_e_955_);
lean_dec_ref(v_e_955_);
return v_res_956_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___redArg(lean_object* v_e_959_, lean_object* v_i_960_){
_start:
{
lean_object* v___x_974_; lean_object* v___x_975_; uint8_t v___x_976_; 
v___x_974_ = ((lean_object*)(l_Lean_Meta_mkPProdMk___closed__1));
v___x_975_ = lean_unsigned_to_nat(4u);
v___x_976_ = l_Lean_Expr_isAppOfArity(v_e_959_, v___x_974_, v___x_975_);
if (v___x_976_ == 0)
{
lean_object* v___x_977_; lean_object* v___x_978_; uint8_t v___x_979_; 
v___x_977_ = ((lean_object*)(l_Lean_Meta_mkPProdMk___closed__3));
v___x_978_ = lean_unsigned_to_nat(2u);
v___x_979_ = l_Lean_Expr_isAppOfArity(v_e_959_, v___x_977_, v___x_978_);
if (v___x_979_ == 0)
{
lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_980_ = ((lean_object*)(l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___redArg___closed__0));
v___x_981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_981_, 0, v___x_980_);
return v___x_981_;
}
else
{
goto v___jp_962_;
}
}
else
{
goto v___jp_962_;
}
v___jp_962_:
{
lean_object* v___x_963_; uint8_t v___x_964_; 
v___x_963_ = lean_unsigned_to_nat(0u);
v___x_964_ = lean_nat_dec_eq(v_i_960_, v___x_963_);
if (v___x_964_ == 0)
{
lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_965_ = l_Lean_Expr_appArg_x21(v_e_959_);
v___x_966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_966_, 0, v___x_965_);
v___x_967_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_967_, 0, v___x_966_);
v___x_968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_968_, 0, v___x_967_);
return v___x_968_;
}
else
{
lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_969_ = l_Lean_Expr_appFn_x21(v_e_959_);
v___x_970_ = l_Lean_Expr_appArg_x21(v___x_969_);
lean_dec_ref(v___x_969_);
v___x_971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_971_, 0, v___x_970_);
v___x_972_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_972_, 0, v___x_971_);
v___x_973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_973_, 0, v___x_972_);
return v___x_973_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___redArg___boxed(lean_object* v_e_982_, lean_object* v_i_983_, lean_object* v_a_984_){
_start:
{
lean_object* v_res_985_; 
v_res_985_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___redArg(v_e_982_, v_i_983_);
lean_dec(v_i_983_);
lean_dec_ref(v_e_982_);
return v_res_985_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce(lean_object* v_e_986_, lean_object* v_i_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_){
_start:
{
lean_object* v___x_993_; 
v___x_993_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___redArg(v_e_986_, v_i_987_);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___boxed(lean_object* v_e_994_, lean_object* v_i_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce(v_e_994_, v_i_995_, v_a_996_, v_a_997_, v_a_998_, v_a_999_);
lean_dec(v_a_999_);
lean_dec_ref(v_a_998_);
lean_dec(v_a_997_);
lean_dec_ref(v_a_996_);
lean_dec(v_i_995_);
lean_dec_ref(v_e_994_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_reduceProjs___lam__0(lean_object* v_x_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_){
_start:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1008_ = ((lean_object*)(l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___redArg___closed__0));
v___x_1009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1008_);
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_reduceProjs___lam__0___boxed(lean_object* v_x_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = l_Lean_Meta_PProdN_reduceProjs___lam__0(v_x_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_);
lean_dec(v___y_1014_);
lean_dec_ref(v___y_1013_);
lean_dec(v___y_1012_);
lean_dec_ref(v___y_1011_);
lean_dec_ref(v_x_1010_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_reduceProjs___lam__1(lean_object* v_e_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_){
_start:
{
lean_object* v_e_x27_1040_; lean_object* v_e_x27_1044_; lean_object* v___x_1054_; 
lean_inc_ref(v_e_1033_);
v___x_1054_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1033_, v___y_1035_);
if (lean_obj_tag(v___x_1054_) == 0)
{
lean_object* v_a_1055_; lean_object* v___x_1056_; uint8_t v___x_1057_; 
v_a_1055_ = lean_ctor_get(v___x_1054_, 0);
lean_inc(v_a_1055_);
lean_dec_ref_known(v___x_1054_, 1);
v___x_1056_ = l_Lean_Expr_cleanupAnnotations(v_a_1055_);
v___x_1057_ = l_Lean_Expr_isApp(v___x_1056_);
if (v___x_1057_ == 0)
{
lean_dec_ref(v___x_1056_);
goto v___jp_1047_;
}
else
{
lean_object* v_arg_1058_; lean_object* v___x_1059_; uint8_t v___x_1060_; 
v_arg_1058_ = lean_ctor_get(v___x_1056_, 1);
lean_inc_ref(v_arg_1058_);
v___x_1059_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1056_);
v___x_1060_ = l_Lean_Expr_isApp(v___x_1059_);
if (v___x_1060_ == 0)
{
lean_dec_ref(v___x_1059_);
lean_dec_ref(v_arg_1058_);
goto v___jp_1047_;
}
else
{
lean_object* v___x_1061_; uint8_t v___x_1062_; 
v___x_1061_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1059_);
v___x_1062_ = l_Lean_Expr_isApp(v___x_1061_);
if (v___x_1062_ == 0)
{
lean_dec_ref(v___x_1061_);
lean_dec_ref(v_arg_1058_);
goto v___jp_1047_;
}
else
{
lean_object* v___x_1063_; lean_object* v___x_1064_; uint8_t v___x_1065_; 
v___x_1063_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1061_);
v___x_1064_ = ((lean_object*)(l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__1));
v___x_1065_ = l_Lean_Expr_isConstOf(v___x_1063_, v___x_1064_);
if (v___x_1065_ == 0)
{
lean_object* v___x_1066_; uint8_t v___x_1067_; 
v___x_1066_ = ((lean_object*)(l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__3));
v___x_1067_ = l_Lean_Expr_isConstOf(v___x_1063_, v___x_1066_);
if (v___x_1067_ == 0)
{
lean_object* v___x_1068_; uint8_t v___x_1069_; 
v___x_1068_ = ((lean_object*)(l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__5));
v___x_1069_ = l_Lean_Expr_isConstOf(v___x_1063_, v___x_1068_);
if (v___x_1069_ == 0)
{
lean_object* v___x_1070_; uint8_t v___x_1071_; 
v___x_1070_ = ((lean_object*)(l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__7));
v___x_1071_ = l_Lean_Expr_isConstOf(v___x_1063_, v___x_1070_);
lean_dec_ref(v___x_1063_);
if (v___x_1071_ == 0)
{
lean_dec_ref(v_arg_1058_);
goto v___jp_1047_;
}
else
{
lean_dec_ref(v_e_1033_);
v_e_x27_1044_ = v_arg_1058_;
goto v___jp_1043_;
}
}
else
{
lean_dec_ref(v___x_1063_);
lean_dec_ref(v_e_1033_);
v_e_x27_1044_ = v_arg_1058_;
goto v___jp_1043_;
}
}
else
{
lean_dec_ref(v___x_1063_);
lean_dec_ref(v_e_1033_);
v_e_x27_1040_ = v_arg_1058_;
goto v___jp_1039_;
}
}
else
{
lean_dec_ref(v___x_1063_);
lean_dec_ref(v_e_1033_);
v_e_x27_1040_ = v_arg_1058_;
goto v___jp_1039_;
}
}
}
}
}
else
{
lean_object* v_a_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1079_; 
lean_dec_ref(v_e_1033_);
v_a_1072_ = lean_ctor_get(v___x_1054_, 0);
v_isSharedCheck_1079_ = !lean_is_exclusive(v___x_1054_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_1074_ = v___x_1054_;
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_a_1072_);
lean_dec(v___x_1054_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v___x_1077_; 
if (v_isShared_1075_ == 0)
{
v___x_1077_ = v___x_1074_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_a_1072_);
v___x_1077_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
return v___x_1077_;
}
}
}
v___jp_1039_:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1041_ = lean_unsigned_to_nat(1u);
v___x_1042_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___redArg(v_e_x27_1040_, v___x_1041_);
lean_dec_ref(v_e_x27_1040_);
return v___x_1042_;
}
v___jp_1043_:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1045_ = lean_unsigned_to_nat(0u);
v___x_1046_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___redArg(v_e_x27_1044_, v___x_1045_);
lean_dec_ref(v_e_x27_1044_);
return v___x_1046_;
}
v___jp_1047_:
{
uint8_t v___x_1048_; 
v___x_1048_ = l_Lean_Expr_isProj(v_e_1033_);
if (v___x_1048_ == 0)
{
lean_object* v___x_1049_; lean_object* v___x_1050_; 
lean_dec_ref(v_e_1033_);
v___x_1049_ = ((lean_object*)(l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___redArg___closed__0));
v___x_1050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1050_, 0, v___x_1049_);
return v___x_1050_;
}
else
{
lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1051_ = l_Lean_Expr_projExpr_x21(v_e_1033_);
v___x_1052_ = l_Lean_Expr_projIdx_x21(v_e_1033_);
lean_dec_ref(v_e_1033_);
v___x_1053_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___redArg(v___x_1051_, v___x_1052_);
lean_dec(v___x_1052_);
lean_dec_ref(v___x_1051_);
return v___x_1053_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_reduceProjs___lam__1___boxed(lean_object* v_e_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_){
_start:
{
lean_object* v_res_1086_; 
v_res_1086_ = l_Lean_Meta_PProdN_reduceProjs___lam__1(v_e_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_);
lean_dec(v___y_1084_);
lean_dec_ref(v___y_1083_);
lean_dec(v___y_1082_);
lean_dec_ref(v___y_1081_);
return v_res_1086_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3_spec__4___redArg(lean_object* v_a_1087_, lean_object* v_x_1088_){
_start:
{
if (lean_obj_tag(v_x_1088_) == 0)
{
lean_object* v___x_1089_; 
v___x_1089_ = lean_box(0);
return v___x_1089_;
}
else
{
lean_object* v_key_1090_; lean_object* v_value_1091_; lean_object* v_tail_1092_; uint8_t v___x_1093_; 
v_key_1090_ = lean_ctor_get(v_x_1088_, 0);
v_value_1091_ = lean_ctor_get(v_x_1088_, 1);
v_tail_1092_ = lean_ctor_get(v_x_1088_, 2);
v___x_1093_ = l_Lean_ExprStructEq_beq(v_key_1090_, v_a_1087_);
if (v___x_1093_ == 0)
{
v_x_1088_ = v_tail_1092_;
goto _start;
}
else
{
lean_object* v___x_1095_; 
lean_inc(v_value_1091_);
v___x_1095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1095_, 0, v_value_1091_);
return v___x_1095_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object* v_a_1096_, lean_object* v_x_1097_){
_start:
{
lean_object* v_res_1098_; 
v_res_1098_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3_spec__4___redArg(v_a_1096_, v_x_1097_);
lean_dec(v_x_1097_);
lean_dec_ref(v_a_1096_);
return v_res_1098_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3___redArg(lean_object* v_m_1099_, lean_object* v_a_1100_){
_start:
{
lean_object* v_buckets_1101_; lean_object* v___x_1102_; uint64_t v___x_1103_; uint64_t v___x_1104_; uint64_t v___x_1105_; uint64_t v_fold_1106_; uint64_t v___x_1107_; uint64_t v___x_1108_; uint64_t v___x_1109_; size_t v___x_1110_; size_t v___x_1111_; size_t v___x_1112_; size_t v___x_1113_; size_t v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; 
v_buckets_1101_ = lean_ctor_get(v_m_1099_, 1);
v___x_1102_ = lean_array_get_size(v_buckets_1101_);
v___x_1103_ = l_Lean_ExprStructEq_hash(v_a_1100_);
v___x_1104_ = 32ULL;
v___x_1105_ = lean_uint64_shift_right(v___x_1103_, v___x_1104_);
v_fold_1106_ = lean_uint64_xor(v___x_1103_, v___x_1105_);
v___x_1107_ = 16ULL;
v___x_1108_ = lean_uint64_shift_right(v_fold_1106_, v___x_1107_);
v___x_1109_ = lean_uint64_xor(v_fold_1106_, v___x_1108_);
v___x_1110_ = lean_uint64_to_usize(v___x_1109_);
v___x_1111_ = lean_usize_of_nat(v___x_1102_);
v___x_1112_ = ((size_t)1ULL);
v___x_1113_ = lean_usize_sub(v___x_1111_, v___x_1112_);
v___x_1114_ = lean_usize_land(v___x_1110_, v___x_1113_);
v___x_1115_ = lean_array_uget_borrowed(v_buckets_1101_, v___x_1114_);
v___x_1116_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3_spec__4___redArg(v_a_1100_, v___x_1115_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_m_1117_, lean_object* v_a_1118_){
_start:
{
lean_object* v_res_1119_; 
v_res_1119_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3___redArg(v_m_1117_, v_a_1118_);
lean_dec_ref(v_a_1118_);
lean_dec_ref(v_m_1117_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__12___redArg(lean_object* v_a_1120_, lean_object* v_b_1121_, lean_object* v_x_1122_){
_start:
{
if (lean_obj_tag(v_x_1122_) == 0)
{
lean_dec(v_b_1121_);
lean_dec_ref(v_a_1120_);
return v_x_1122_;
}
else
{
lean_object* v_key_1123_; lean_object* v_value_1124_; lean_object* v_tail_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1137_; 
v_key_1123_ = lean_ctor_get(v_x_1122_, 0);
v_value_1124_ = lean_ctor_get(v_x_1122_, 1);
v_tail_1125_ = lean_ctor_get(v_x_1122_, 2);
v_isSharedCheck_1137_ = !lean_is_exclusive(v_x_1122_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1127_ = v_x_1122_;
v_isShared_1128_ = v_isSharedCheck_1137_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_tail_1125_);
lean_inc(v_value_1124_);
lean_inc(v_key_1123_);
lean_dec(v_x_1122_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1137_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
uint8_t v___x_1129_; 
v___x_1129_ = l_Lean_ExprStructEq_beq(v_key_1123_, v_a_1120_);
if (v___x_1129_ == 0)
{
lean_object* v___x_1130_; lean_object* v___x_1132_; 
v___x_1130_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__12___redArg(v_a_1120_, v_b_1121_, v_tail_1125_);
if (v_isShared_1128_ == 0)
{
lean_ctor_set(v___x_1127_, 2, v___x_1130_);
v___x_1132_ = v___x_1127_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v_key_1123_);
lean_ctor_set(v_reuseFailAlloc_1133_, 1, v_value_1124_);
lean_ctor_set(v_reuseFailAlloc_1133_, 2, v___x_1130_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
else
{
lean_object* v___x_1135_; 
lean_dec(v_value_1124_);
lean_dec(v_key_1123_);
if (v_isShared_1128_ == 0)
{
lean_ctor_set(v___x_1127_, 1, v_b_1121_);
lean_ctor_set(v___x_1127_, 0, v_a_1120_);
v___x_1135_ = v___x_1127_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v_a_1120_);
lean_ctor_set(v_reuseFailAlloc_1136_, 1, v_b_1121_);
lean_ctor_set(v_reuseFailAlloc_1136_, 2, v_tail_1125_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(lean_object* v_x_1138_, lean_object* v_x_1139_){
_start:
{
if (lean_obj_tag(v_x_1139_) == 0)
{
return v_x_1138_;
}
else
{
lean_object* v_key_1140_; lean_object* v_value_1141_; lean_object* v_tail_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1165_; 
v_key_1140_ = lean_ctor_get(v_x_1139_, 0);
v_value_1141_ = lean_ctor_get(v_x_1139_, 1);
v_tail_1142_ = lean_ctor_get(v_x_1139_, 2);
v_isSharedCheck_1165_ = !lean_is_exclusive(v_x_1139_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1144_ = v_x_1139_;
v_isShared_1145_ = v_isSharedCheck_1165_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_tail_1142_);
lean_inc(v_value_1141_);
lean_inc(v_key_1140_);
lean_dec(v_x_1139_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1165_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1146_; uint64_t v___x_1147_; uint64_t v___x_1148_; uint64_t v___x_1149_; uint64_t v_fold_1150_; uint64_t v___x_1151_; uint64_t v___x_1152_; uint64_t v___x_1153_; size_t v___x_1154_; size_t v___x_1155_; size_t v___x_1156_; size_t v___x_1157_; size_t v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1161_; 
v___x_1146_ = lean_array_get_size(v_x_1138_);
v___x_1147_ = l_Lean_ExprStructEq_hash(v_key_1140_);
v___x_1148_ = 32ULL;
v___x_1149_ = lean_uint64_shift_right(v___x_1147_, v___x_1148_);
v_fold_1150_ = lean_uint64_xor(v___x_1147_, v___x_1149_);
v___x_1151_ = 16ULL;
v___x_1152_ = lean_uint64_shift_right(v_fold_1150_, v___x_1151_);
v___x_1153_ = lean_uint64_xor(v_fold_1150_, v___x_1152_);
v___x_1154_ = lean_uint64_to_usize(v___x_1153_);
v___x_1155_ = lean_usize_of_nat(v___x_1146_);
v___x_1156_ = ((size_t)1ULL);
v___x_1157_ = lean_usize_sub(v___x_1155_, v___x_1156_);
v___x_1158_ = lean_usize_land(v___x_1154_, v___x_1157_);
v___x_1159_ = lean_array_uget_borrowed(v_x_1138_, v___x_1158_);
lean_inc(v___x_1159_);
if (v_isShared_1145_ == 0)
{
lean_ctor_set(v___x_1144_, 2, v___x_1159_);
v___x_1161_ = v___x_1144_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_key_1140_);
lean_ctor_set(v_reuseFailAlloc_1164_, 1, v_value_1141_);
lean_ctor_set(v_reuseFailAlloc_1164_, 2, v___x_1159_);
v___x_1161_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
lean_object* v___x_1162_; 
v___x_1162_ = lean_array_uset(v_x_1138_, v___x_1158_, v___x_1161_);
v_x_1138_ = v___x_1162_;
v_x_1139_ = v_tail_1142_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(lean_object* v_i_1166_, lean_object* v_source_1167_, lean_object* v_target_1168_){
_start:
{
lean_object* v___x_1169_; uint8_t v___x_1170_; 
v___x_1169_ = lean_array_get_size(v_source_1167_);
v___x_1170_ = lean_nat_dec_lt(v_i_1166_, v___x_1169_);
if (v___x_1170_ == 0)
{
lean_dec_ref(v_source_1167_);
lean_dec(v_i_1166_);
return v_target_1168_;
}
else
{
lean_object* v_es_1171_; lean_object* v___x_1172_; lean_object* v_source_1173_; lean_object* v_target_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
v_es_1171_ = lean_array_fget(v_source_1167_, v_i_1166_);
v___x_1172_ = lean_box(0);
v_source_1173_ = lean_array_fset(v_source_1167_, v_i_1166_, v___x_1172_);
v_target_1174_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_target_1168_, v_es_1171_);
v___x_1175_ = lean_unsigned_to_nat(1u);
v___x_1176_ = lean_nat_add(v_i_1166_, v___x_1175_);
lean_dec(v_i_1166_);
v_i_1166_ = v___x_1176_;
v_source_1167_ = v_source_1173_;
v_target_1168_ = v_target_1174_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11___redArg(lean_object* v_data_1178_){
_start:
{
lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v_nbuckets_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; 
v___x_1179_ = lean_array_get_size(v_data_1178_);
v___x_1180_ = lean_unsigned_to_nat(2u);
v_nbuckets_1181_ = lean_nat_mul(v___x_1179_, v___x_1180_);
v___x_1182_ = lean_unsigned_to_nat(0u);
v___x_1183_ = lean_box(0);
v___x_1184_ = lean_mk_array(v_nbuckets_1181_, v___x_1183_);
v___x_1185_ = lean_array_propagate_mark(v_data_1178_, v___x_1184_);
v___x_1186_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v___x_1182_, v_data_1178_, v___x_1185_);
return v___x_1186_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__10___redArg(lean_object* v_a_1187_, lean_object* v_x_1188_){
_start:
{
if (lean_obj_tag(v_x_1188_) == 0)
{
uint8_t v___x_1189_; 
v___x_1189_ = 0;
return v___x_1189_;
}
else
{
lean_object* v_key_1190_; lean_object* v_tail_1191_; uint8_t v___x_1192_; 
v_key_1190_ = lean_ctor_get(v_x_1188_, 0);
v_tail_1191_ = lean_ctor_get(v_x_1188_, 2);
v___x_1192_ = l_Lean_ExprStructEq_beq(v_key_1190_, v_a_1187_);
if (v___x_1192_ == 0)
{
v_x_1188_ = v_tail_1191_;
goto _start;
}
else
{
return v___x_1192_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__10___redArg___boxed(lean_object* v_a_1194_, lean_object* v_x_1195_){
_start:
{
uint8_t v_res_1196_; lean_object* v_r_1197_; 
v_res_1196_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__10___redArg(v_a_1194_, v_x_1195_);
lean_dec(v_x_1195_);
lean_dec_ref(v_a_1194_);
v_r_1197_ = lean_box(v_res_1196_);
return v_r_1197_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6___redArg(lean_object* v_m_1198_, lean_object* v_a_1199_, lean_object* v_b_1200_){
_start:
{
lean_object* v_size_1201_; lean_object* v_buckets_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1245_; 
v_size_1201_ = lean_ctor_get(v_m_1198_, 0);
v_buckets_1202_ = lean_ctor_get(v_m_1198_, 1);
v_isSharedCheck_1245_ = !lean_is_exclusive(v_m_1198_);
if (v_isSharedCheck_1245_ == 0)
{
v___x_1204_ = v_m_1198_;
v_isShared_1205_ = v_isSharedCheck_1245_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_buckets_1202_);
lean_inc(v_size_1201_);
lean_dec(v_m_1198_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1245_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v___x_1206_; uint64_t v___x_1207_; uint64_t v___x_1208_; uint64_t v___x_1209_; uint64_t v_fold_1210_; uint64_t v___x_1211_; uint64_t v___x_1212_; uint64_t v___x_1213_; size_t v___x_1214_; size_t v___x_1215_; size_t v___x_1216_; size_t v___x_1217_; size_t v___x_1218_; lean_object* v_bkt_1219_; uint8_t v___x_1220_; 
v___x_1206_ = lean_array_get_size(v_buckets_1202_);
v___x_1207_ = l_Lean_ExprStructEq_hash(v_a_1199_);
v___x_1208_ = 32ULL;
v___x_1209_ = lean_uint64_shift_right(v___x_1207_, v___x_1208_);
v_fold_1210_ = lean_uint64_xor(v___x_1207_, v___x_1209_);
v___x_1211_ = 16ULL;
v___x_1212_ = lean_uint64_shift_right(v_fold_1210_, v___x_1211_);
v___x_1213_ = lean_uint64_xor(v_fold_1210_, v___x_1212_);
v___x_1214_ = lean_uint64_to_usize(v___x_1213_);
v___x_1215_ = lean_usize_of_nat(v___x_1206_);
v___x_1216_ = ((size_t)1ULL);
v___x_1217_ = lean_usize_sub(v___x_1215_, v___x_1216_);
v___x_1218_ = lean_usize_land(v___x_1214_, v___x_1217_);
v_bkt_1219_ = lean_array_uget_borrowed(v_buckets_1202_, v___x_1218_);
v___x_1220_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__10___redArg(v_a_1199_, v_bkt_1219_);
if (v___x_1220_ == 0)
{
lean_object* v___x_1221_; lean_object* v_size_x27_1222_; lean_object* v___x_1223_; lean_object* v_buckets_x27_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; uint8_t v___x_1230_; 
v___x_1221_ = lean_unsigned_to_nat(1u);
v_size_x27_1222_ = lean_nat_add(v_size_1201_, v___x_1221_);
lean_dec(v_size_1201_);
lean_inc(v_bkt_1219_);
v___x_1223_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1223_, 0, v_a_1199_);
lean_ctor_set(v___x_1223_, 1, v_b_1200_);
lean_ctor_set(v___x_1223_, 2, v_bkt_1219_);
v_buckets_x27_1224_ = lean_array_uset(v_buckets_1202_, v___x_1218_, v___x_1223_);
v___x_1225_ = lean_unsigned_to_nat(4u);
v___x_1226_ = lean_nat_mul(v_size_x27_1222_, v___x_1225_);
v___x_1227_ = lean_unsigned_to_nat(3u);
v___x_1228_ = lean_nat_div(v___x_1226_, v___x_1227_);
lean_dec(v___x_1226_);
v___x_1229_ = lean_array_get_size(v_buckets_x27_1224_);
v___x_1230_ = lean_nat_dec_le(v___x_1228_, v___x_1229_);
lean_dec(v___x_1228_);
if (v___x_1230_ == 0)
{
lean_object* v_val_1231_; lean_object* v___x_1233_; 
v_val_1231_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11___redArg(v_buckets_x27_1224_);
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 1, v_val_1231_);
lean_ctor_set(v___x_1204_, 0, v_size_x27_1222_);
v___x_1233_ = v___x_1204_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v_size_x27_1222_);
lean_ctor_set(v_reuseFailAlloc_1234_, 1, v_val_1231_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
return v___x_1233_;
}
}
else
{
lean_object* v___x_1236_; 
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 1, v_buckets_x27_1224_);
lean_ctor_set(v___x_1204_, 0, v_size_x27_1222_);
v___x_1236_ = v___x_1204_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v_size_x27_1222_);
lean_ctor_set(v_reuseFailAlloc_1237_, 1, v_buckets_x27_1224_);
v___x_1236_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
return v___x_1236_;
}
}
}
else
{
lean_object* v___x_1238_; lean_object* v_buckets_x27_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1243_; 
lean_inc(v_bkt_1219_);
v___x_1238_ = lean_box(0);
v_buckets_x27_1239_ = lean_array_uset(v_buckets_1202_, v___x_1218_, v___x_1238_);
v___x_1240_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__12___redArg(v_a_1199_, v_b_1200_, v_bkt_1219_);
v___x_1241_ = lean_array_uset(v_buckets_x27_1239_, v___x_1218_, v___x_1240_);
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 1, v___x_1241_);
v___x_1243_ = v___x_1204_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v_size_1201_);
lean_ctor_set(v_reuseFailAlloc_1244_, 1, v___x_1241_);
v___x_1243_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
return v___x_1243_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__2(lean_object* v_a_1246_, lean_object* v_e_1247_, lean_object* v_a_1248_){
_start:
{
lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1250_ = lean_st_ref_take(v_a_1246_);
v___x_1251_ = lean_box(0);
v___x_1252_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6___redArg(v___x_1250_, v_e_1247_, v_a_1248_);
v___x_1253_ = lean_st_ref_put(v_a_1246_, v___x_1252_);
return v___x_1251_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__2___boxed(lean_object* v_a_1254_, lean_object* v_e_1255_, lean_object* v_a_1256_, lean_object* v___y_1257_){
_start:
{
lean_object* v_res_1258_; 
v_res_1258_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__2(v_a_1254_, v_e_1255_, v_a_1256_);
lean_dec(v_a_1254_);
return v_res_1258_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_1259_, lean_object* v_x_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_){
_start:
{
lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1266_ = lean_apply_1(v_x_1260_, lean_box(0));
v___x_1267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1267_, 0, v___x_1266_);
return v___x_1267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_1268_, lean_object* v_x_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_){
_start:
{
lean_object* v_res_1275_; 
v_res_1275_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__0(v_00_u03b1_1268_, v_x_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_);
lean_dec(v___y_1273_);
lean_dec_ref(v___y_1272_);
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1270_);
return v_res_1275_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___x_1276_ = lean_box(0);
v___x_1277_ = l_Lean_interruptExceptionId;
v___x_1278_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1277_);
lean_ctor_set(v___x_1278_, 1, v___x_1276_);
return v___x_1278_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__8___redArg(){
_start:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; 
v___x_1280_ = lean_obj_once(&l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__8___redArg___closed__0, &l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__8___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__8___redArg___closed__0);
v___x_1281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1280_);
return v___x_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__8___redArg___boxed(lean_object* v___y_1282_){
_start:
{
lean_object* v_res_1283_; 
v_res_1283_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__8___redArg();
return v_res_1283_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1289_ = l_Lean_maxRecDepthErrorMessage;
v___x_1290_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1290_, 0, v___x_1289_);
return v___x_1290_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1291_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__3);
v___x_1292_ = l_Lean_MessageData_ofFormat(v___x_1291_);
return v___x_1292_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1293_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__4);
v___x_1294_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__2));
v___x_1295_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1295_, 0, v___x_1294_);
lean_ctor_set(v___x_1295_, 1, v___x_1293_);
return v___x_1295_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg(lean_object* v_ref_1296_){
_start:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1298_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__5);
v___x_1299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1299_, 0, v_ref_1296_);
lean_ctor_set(v___x_1299_, 1, v___x_1298_);
v___x_1300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1300_, 0, v___x_1299_);
return v___x_1300_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object* v_ref_1301_, lean_object* v___y_1302_){
_start:
{
lean_object* v_res_1303_; 
v_res_1303_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_1301_);
return v_res_1303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5___redArg(lean_object* v_x_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_){
_start:
{
lean_object* v___y_1312_; lean_object* v___y_1322_; uint16_t v___y_1323_; uint8_t v___y_1324_; lean_object* v___y_1325_; uint8_t v___y_1326_; lean_object* v___y_1327_; lean_object* v_toCold_1332_; lean_object* v_currRecDepth_1333_; lean_object* v_ref_1334_; uint16_t v_optionFlags_1335_; uint8_t v_suppressElabErrors_1336_; uint8_t v_isRecordingDeps_1337_; lean_object* v_maxRecDepth_1338_; lean_object* v_cancelTk_x3f_1339_; 
v_toCold_1332_ = lean_ctor_get(v___y_1308_, 0);
v_currRecDepth_1333_ = lean_ctor_get(v___y_1308_, 1);
v_ref_1334_ = lean_ctor_get(v___y_1308_, 2);
v_optionFlags_1335_ = lean_ctor_get_uint16(v___y_1308_, sizeof(void*)*3);
v_suppressElabErrors_1336_ = lean_ctor_get_uint8(v___y_1308_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1337_ = lean_ctor_get_uint8(v___y_1308_, sizeof(void*)*3 + 3);
v_maxRecDepth_1338_ = lean_ctor_get(v_toCold_1332_, 3);
v_cancelTk_x3f_1339_ = lean_ctor_get(v_toCold_1332_, 10);
if (lean_obj_tag(v_cancelTk_x3f_1339_) == 1)
{
lean_object* v_val_1345_; uint8_t v___x_1346_; 
v_val_1345_ = lean_ctor_get(v_cancelTk_x3f_1339_, 0);
v___x_1346_ = l_IO_CancelToken_isSet(v_val_1345_);
if (v___x_1346_ == 0)
{
goto v___jp_1340_;
}
else
{
lean_object* v___x_1347_; lean_object* v_a_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1355_; 
lean_dec_ref(v_x_1304_);
v___x_1347_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__8___redArg();
v_a_1348_ = lean_ctor_get(v___x_1347_, 0);
v_isSharedCheck_1355_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1355_ == 0)
{
v___x_1350_ = v___x_1347_;
v_isShared_1351_ = v_isSharedCheck_1355_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_a_1348_);
lean_dec(v___x_1347_);
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
else
{
goto v___jp_1340_;
}
v___jp_1311_:
{
if (lean_obj_tag(v___y_1312_) == 0)
{
return v___y_1312_;
}
else
{
lean_object* v_a_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1320_; 
v_a_1313_ = lean_ctor_get(v___y_1312_, 0);
v_isSharedCheck_1320_ = !lean_is_exclusive(v___y_1312_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1315_ = v___y_1312_;
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_a_1313_);
lean_dec(v___y_1312_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v___x_1318_; 
if (v_isShared_1316_ == 0)
{
v___x_1318_ = v___x_1315_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v_a_1313_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
return v___x_1318_;
}
}
}
}
v___jp_1321_:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; 
v___x_1328_ = lean_unsigned_to_nat(1u);
v___x_1329_ = lean_nat_add(v___y_1322_, v___x_1328_);
lean_inc_ref(v___y_1325_);
v___x_1330_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1330_, 0, v___y_1325_);
lean_ctor_set(v___x_1330_, 1, v___x_1329_);
lean_ctor_set(v___x_1330_, 2, v___y_1327_);
lean_ctor_set_uint16(v___x_1330_, sizeof(void*)*3, v___y_1323_);
lean_ctor_set_uint8(v___x_1330_, sizeof(void*)*3 + 2, v___y_1326_);
lean_ctor_set_uint8(v___x_1330_, sizeof(void*)*3 + 3, v___y_1324_);
lean_inc(v___y_1309_);
lean_inc(v___y_1307_);
lean_inc_ref(v___y_1306_);
lean_inc(v___y_1305_);
v___x_1331_ = lean_apply_6(v_x_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___x_1330_, v___y_1309_, lean_box(0));
v___y_1312_ = v___x_1331_;
goto v___jp_1311_;
}
v___jp_1340_:
{
lean_object* v___x_1341_; uint8_t v___x_1342_; 
v___x_1341_ = lean_unsigned_to_nat(0u);
v___x_1342_ = lean_nat_dec_eq(v_maxRecDepth_1338_, v___x_1341_);
if (v___x_1342_ == 0)
{
uint8_t v___x_1343_; 
v___x_1343_ = lean_nat_dec_eq(v_currRecDepth_1333_, v_maxRecDepth_1338_);
if (v___x_1343_ == 0)
{
lean_inc(v_ref_1334_);
v___y_1322_ = v_currRecDepth_1333_;
v___y_1323_ = v_optionFlags_1335_;
v___y_1324_ = v_isRecordingDeps_1337_;
v___y_1325_ = v_toCold_1332_;
v___y_1326_ = v_suppressElabErrors_1336_;
v___y_1327_ = v_ref_1334_;
goto v___jp_1321_;
}
else
{
lean_object* v___x_1344_; 
lean_dec_ref(v_x_1304_);
lean_inc(v_ref_1334_);
v___x_1344_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_1334_);
v___y_1312_ = v___x_1344_;
goto v___jp_1311_;
}
}
else
{
lean_inc(v_ref_1334_);
v___y_1322_ = v_currRecDepth_1333_;
v___y_1323_ = v_optionFlags_1335_;
v___y_1324_ = v_isRecordingDeps_1337_;
v___y_1325_ = v_toCold_1332_;
v___y_1326_ = v_suppressElabErrors_1336_;
v___y_1327_ = v_ref_1334_;
goto v___jp_1321_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_x_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_){
_start:
{
lean_object* v_res_1363_; 
v_res_1363_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5___redArg(v_x_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_);
lean_dec(v___y_1361_);
lean_dec_ref(v___y_1360_);
lean_dec(v___y_1359_);
lean_dec_ref(v___y_1358_);
lean_dec(v___y_1357_);
return v_res_1363_;
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__1___closed__0(void){
_start:
{
lean_object* v___x_1365_; lean_object* v_dummy_1366_; 
v___x_1365_ = lean_box(0);
v_dummy_1366_ = l_Lean_Expr_sort___override(v___x_1365_);
return v_dummy_1366_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__1(lean_object* v_pre_1367_, lean_object* v_post_1368_, size_t v_sz_1369_, size_t v_i_1370_, lean_object* v_bs_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_){
_start:
{
uint8_t v___x_1378_; 
v___x_1378_ = lean_usize_dec_lt(v_i_1370_, v_sz_1369_);
if (v___x_1378_ == 0)
{
lean_object* v___x_1379_; 
lean_dec_ref(v_post_1368_);
lean_dec_ref(v_pre_1367_);
v___x_1379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1379_, 0, v_bs_1371_);
return v___x_1379_;
}
else
{
lean_object* v_v_1380_; lean_object* v___x_1381_; lean_object* v_bs_x27_1382_; lean_object* v___x_1383_; 
v_v_1380_ = lean_array_uget(v_bs_1371_, v_i_1370_);
v___x_1381_ = lean_unsigned_to_nat(0u);
v_bs_x27_1382_ = lean_array_uset(v_bs_1371_, v_i_1370_, v___x_1381_);
lean_inc_ref(v_post_1368_);
lean_inc_ref(v_pre_1367_);
v___x_1383_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1367_, v_post_1368_, v_v_1380_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_);
if (lean_obj_tag(v___x_1383_) == 0)
{
lean_object* v_a_1384_; size_t v___x_1385_; size_t v___x_1386_; lean_object* v___x_1387_; 
v_a_1384_ = lean_ctor_get(v___x_1383_, 0);
lean_inc(v_a_1384_);
lean_dec_ref_known(v___x_1383_, 1);
v___x_1385_ = ((size_t)1ULL);
v___x_1386_ = lean_usize_add(v_i_1370_, v___x_1385_);
v___x_1387_ = lean_array_uset(v_bs_x27_1382_, v_i_1370_, v_a_1384_);
v_i_1370_ = v___x_1386_;
v_bs_1371_ = v___x_1387_;
goto _start;
}
else
{
lean_object* v_a_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1396_; 
lean_dec_ref(v_bs_x27_1382_);
lean_dec_ref(v_post_1368_);
lean_dec_ref(v_pre_1367_);
v_a_1389_ = lean_ctor_get(v___x_1383_, 0);
v_isSharedCheck_1396_ = !lean_is_exclusive(v___x_1383_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1391_ = v___x_1383_;
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_a_1389_);
lean_dec(v___x_1383_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1394_; 
if (v_isShared_1392_ == 0)
{
v___x_1394_ = v___x_1391_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v_a_1389_);
v___x_1394_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
return v___x_1394_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__4(lean_object* v_pre_1397_, lean_object* v_post_1398_, lean_object* v_x_1399_, lean_object* v_x_1400_, lean_object* v_x_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_){
_start:
{
if (lean_obj_tag(v_x_1399_) == 5)
{
lean_object* v_fn_1408_; lean_object* v_arg_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; 
v_fn_1408_ = lean_ctor_get(v_x_1399_, 0);
lean_inc_ref(v_fn_1408_);
v_arg_1409_ = lean_ctor_get(v_x_1399_, 1);
lean_inc_ref(v_arg_1409_);
lean_dec_ref_known(v_x_1399_, 2);
v___x_1410_ = lean_array_set(v_x_1400_, v_x_1401_, v_arg_1409_);
v___x_1411_ = lean_unsigned_to_nat(1u);
v___x_1412_ = lean_nat_sub(v_x_1401_, v___x_1411_);
lean_dec(v_x_1401_);
v_x_1399_ = v_fn_1408_;
v_x_1400_ = v___x_1410_;
v_x_1401_ = v___x_1412_;
goto _start;
}
else
{
lean_object* v___x_1414_; 
lean_dec(v_x_1401_);
lean_inc_ref(v_post_1398_);
lean_inc_ref(v_pre_1397_);
v___x_1414_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1397_, v_post_1398_, v_x_1399_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_);
if (lean_obj_tag(v___x_1414_) == 0)
{
lean_object* v_a_1415_; size_t v_sz_1416_; size_t v___x_1417_; lean_object* v___x_1418_; 
v_a_1415_ = lean_ctor_get(v___x_1414_, 0);
lean_inc(v_a_1415_);
lean_dec_ref_known(v___x_1414_, 1);
v_sz_1416_ = lean_array_size(v_x_1400_);
v___x_1417_ = ((size_t)0ULL);
lean_inc_ref(v_post_1398_);
lean_inc_ref(v_pre_1397_);
v___x_1418_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__1(v_pre_1397_, v_post_1398_, v_sz_1416_, v___x_1417_, v_x_1400_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_);
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_object* v_a_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; 
v_a_1419_ = lean_ctor_get(v___x_1418_, 0);
lean_inc(v_a_1419_);
lean_dec_ref_known(v___x_1418_, 1);
v___x_1420_ = l_Lean_mkAppN(v_a_1415_, v_a_1419_);
lean_dec(v_a_1419_);
v___x_1421_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1397_, v_post_1398_, v___x_1420_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_);
return v___x_1421_;
}
else
{
lean_object* v_a_1422_; lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1429_; 
lean_dec(v_a_1415_);
lean_dec_ref(v_post_1398_);
lean_dec_ref(v_pre_1397_);
v_a_1422_ = lean_ctor_get(v___x_1418_, 0);
v_isSharedCheck_1429_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1424_ = v___x_1418_;
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
else
{
lean_inc(v_a_1422_);
lean_dec(v___x_1418_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
lean_object* v___x_1427_; 
if (v_isShared_1425_ == 0)
{
v___x_1427_ = v___x_1424_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_a_1422_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
return v___x_1427_;
}
}
}
}
else
{
lean_dec_ref(v_x_1400_);
lean_dec_ref(v_post_1398_);
lean_dec_ref(v_pre_1397_);
return v___x_1414_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__1(lean_object* v___x_1430_, lean_object* v_pre_1431_, lean_object* v_e_1432_, lean_object* v_post_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_){
_start:
{
lean_object* v___x_1440_; 
v___x_1440_ = l_Lean_Core_checkSystem(v___x_1430_, v___y_1437_, v___y_1438_);
if (lean_obj_tag(v___x_1440_) == 0)
{
lean_object* v___x_1441_; 
lean_dec_ref_known(v___x_1440_, 1);
lean_inc_ref(v_pre_1431_);
lean_inc(v___y_1438_);
lean_inc_ref(v___y_1437_);
lean_inc(v___y_1436_);
lean_inc_ref(v___y_1435_);
lean_inc_ref(v_e_1432_);
v___x_1441_ = lean_apply_6(v_pre_1431_, v_e_1432_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, lean_box(0));
if (lean_obj_tag(v___x_1441_) == 0)
{
lean_object* v_a_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1557_; 
v_a_1442_ = lean_ctor_get(v___x_1441_, 0);
v_isSharedCheck_1557_ = !lean_is_exclusive(v___x_1441_);
if (v_isSharedCheck_1557_ == 0)
{
v___x_1444_ = v___x_1441_;
v_isShared_1445_ = v_isSharedCheck_1557_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_a_1442_);
lean_dec(v___x_1441_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1557_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___y_1447_; 
switch(lean_obj_tag(v_a_1442_))
{
case 0:
{
lean_object* v_e_1547_; lean_object* v___x_1549_; 
lean_dec_ref(v_post_1433_);
lean_dec_ref(v_e_1432_);
lean_dec_ref(v_pre_1431_);
v_e_1547_ = lean_ctor_get(v_a_1442_, 0);
lean_inc_ref(v_e_1547_);
lean_dec_ref_known(v_a_1442_, 1);
if (v_isShared_1445_ == 0)
{
lean_ctor_set(v___x_1444_, 0, v_e_1547_);
v___x_1549_ = v___x_1444_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v_e_1547_);
v___x_1549_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
return v___x_1549_;
}
}
case 1:
{
lean_object* v_e_1551_; lean_object* v___x_1552_; 
lean_del_object(v___x_1444_);
lean_dec_ref(v_e_1432_);
v_e_1551_ = lean_ctor_get(v_a_1442_, 0);
lean_inc_ref(v_e_1551_);
lean_dec_ref_known(v_a_1442_, 1);
lean_inc_ref(v_post_1433_);
lean_inc_ref(v_pre_1431_);
v___x_1552_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1431_, v_post_1433_, v_e_1551_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
if (lean_obj_tag(v___x_1552_) == 0)
{
lean_object* v_a_1553_; lean_object* v___x_1554_; 
v_a_1553_ = lean_ctor_get(v___x_1552_, 0);
lean_inc(v_a_1553_);
lean_dec_ref_known(v___x_1552_, 1);
v___x_1554_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1431_, v_post_1433_, v_a_1553_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
return v___x_1554_;
}
else
{
lean_dec_ref(v_post_1433_);
lean_dec_ref(v_pre_1431_);
return v___x_1552_;
}
}
default: 
{
lean_object* v_e_x3f_1555_; 
lean_del_object(v___x_1444_);
v_e_x3f_1555_ = lean_ctor_get(v_a_1442_, 0);
lean_inc(v_e_x3f_1555_);
lean_dec_ref_known(v_a_1442_, 1);
if (lean_obj_tag(v_e_x3f_1555_) == 0)
{
v___y_1447_ = v_e_1432_;
goto v___jp_1446_;
}
else
{
lean_object* v_val_1556_; 
lean_dec_ref(v_e_1432_);
v_val_1556_ = lean_ctor_get(v_e_x3f_1555_, 0);
lean_inc(v_val_1556_);
lean_dec_ref_known(v_e_x3f_1555_, 1);
v___y_1447_ = v_val_1556_;
goto v___jp_1446_;
}
}
}
v___jp_1446_:
{
switch(lean_obj_tag(v___y_1447_))
{
case 7:
{
lean_object* v_binderName_1448_; lean_object* v_binderType_1449_; lean_object* v_body_1450_; uint8_t v_binderInfo_1451_; lean_object* v___x_1452_; 
v_binderName_1448_ = lean_ctor_get(v___y_1447_, 0);
v_binderType_1449_ = lean_ctor_get(v___y_1447_, 1);
v_body_1450_ = lean_ctor_get(v___y_1447_, 2);
v_binderInfo_1451_ = lean_ctor_get_uint8(v___y_1447_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1449_);
lean_inc_ref(v_post_1433_);
lean_inc_ref(v_pre_1431_);
v___x_1452_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1431_, v_post_1433_, v_binderType_1449_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
if (lean_obj_tag(v___x_1452_) == 0)
{
lean_object* v_a_1453_; lean_object* v___x_1454_; 
v_a_1453_ = lean_ctor_get(v___x_1452_, 0);
lean_inc(v_a_1453_);
lean_dec_ref_known(v___x_1452_, 1);
lean_inc_ref(v_body_1450_);
lean_inc_ref(v_post_1433_);
lean_inc_ref(v_pre_1431_);
v___x_1454_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1431_, v_post_1433_, v_body_1450_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
if (lean_obj_tag(v___x_1454_) == 0)
{
lean_object* v_a_1455_; size_t v___x_1456_; size_t v___x_1457_; uint8_t v___x_1458_; 
v_a_1455_ = lean_ctor_get(v___x_1454_, 0);
lean_inc(v_a_1455_);
lean_dec_ref_known(v___x_1454_, 1);
v___x_1456_ = lean_ptr_addr(v_binderType_1449_);
v___x_1457_ = lean_ptr_addr(v_a_1453_);
v___x_1458_ = lean_usize_dec_eq(v___x_1456_, v___x_1457_);
if (v___x_1458_ == 0)
{
lean_object* v___x_1459_; lean_object* v___x_1460_; 
lean_inc(v_binderName_1448_);
lean_dec_ref_known(v___y_1447_, 3);
v___x_1459_ = l_Lean_Expr_forallE___override(v_binderName_1448_, v_a_1453_, v_a_1455_, v_binderInfo_1451_);
v___x_1460_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1431_, v_post_1433_, v___x_1459_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
return v___x_1460_;
}
else
{
size_t v___x_1461_; size_t v___x_1462_; uint8_t v___x_1463_; 
v___x_1461_ = lean_ptr_addr(v_body_1450_);
v___x_1462_ = lean_ptr_addr(v_a_1455_);
v___x_1463_ = lean_usize_dec_eq(v___x_1461_, v___x_1462_);
if (v___x_1463_ == 0)
{
lean_object* v___x_1464_; lean_object* v___x_1465_; 
lean_inc(v_binderName_1448_);
lean_dec_ref_known(v___y_1447_, 3);
v___x_1464_ = l_Lean_Expr_forallE___override(v_binderName_1448_, v_a_1453_, v_a_1455_, v_binderInfo_1451_);
v___x_1465_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1431_, v_post_1433_, v___x_1464_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
return v___x_1465_;
}
else
{
uint8_t v___x_1466_; 
v___x_1466_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1451_, v_binderInfo_1451_);
if (v___x_1466_ == 0)
{
lean_object* v___x_1467_; lean_object* v___x_1468_; 
lean_inc(v_binderName_1448_);
lean_dec_ref_known(v___y_1447_, 3);
v___x_1467_ = l_Lean_Expr_forallE___override(v_binderName_1448_, v_a_1453_, v_a_1455_, v_binderInfo_1451_);
v___x_1468_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1431_, v_post_1433_, v___x_1467_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
return v___x_1468_;
}
else
{
lean_object* v___x_1469_; 
lean_dec(v_a_1455_);
lean_dec(v_a_1453_);
v___x_1469_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1431_, v_post_1433_, v___y_1447_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
return v___x_1469_;
}
}
}
}
else
{
lean_dec(v_a_1453_);
lean_dec_ref_known(v___y_1447_, 3);
lean_dec_ref(v_post_1433_);
lean_dec_ref(v_pre_1431_);
return v___x_1454_;
}
}
else
{
lean_dec_ref_known(v___y_1447_, 3);
lean_dec_ref(v_post_1433_);
lean_dec_ref(v_pre_1431_);
return v___x_1452_;
}
}
case 6:
{
lean_object* v_binderName_1470_; lean_object* v_binderType_1471_; lean_object* v_body_1472_; uint8_t v_binderInfo_1473_; lean_object* v___x_1474_; 
v_binderName_1470_ = lean_ctor_get(v___y_1447_, 0);
v_binderType_1471_ = lean_ctor_get(v___y_1447_, 1);
v_body_1472_ = lean_ctor_get(v___y_1447_, 2);
v_binderInfo_1473_ = lean_ctor_get_uint8(v___y_1447_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1471_);
lean_inc_ref(v_post_1433_);
lean_inc_ref(v_pre_1431_);
v___x_1474_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1431_, v_post_1433_, v_binderType_1471_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
if (lean_obj_tag(v___x_1474_) == 0)
{
lean_object* v_a_1475_; lean_object* v___x_1476_; 
v_a_1475_ = lean_ctor_get(v___x_1474_, 0);
lean_inc(v_a_1475_);
lean_dec_ref_known(v___x_1474_, 1);
lean_inc_ref(v_body_1472_);
lean_inc_ref(v_post_1433_);
lean_inc_ref(v_pre_1431_);
v___x_1476_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1431_, v_post_1433_, v_body_1472_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
if (lean_obj_tag(v___x_1476_) == 0)
{
lean_object* v_a_1477_; size_t v___x_1478_; size_t v___x_1479_; uint8_t v___x_1480_; 
v_a_1477_ = lean_ctor_get(v___x_1476_, 0);
lean_inc(v_a_1477_);
lean_dec_ref_known(v___x_1476_, 1);
v___x_1478_ = lean_ptr_addr(v_binderType_1471_);
v___x_1479_ = lean_ptr_addr(v_a_1475_);
v___x_1480_ = lean_usize_dec_eq(v___x_1478_, v___x_1479_);
if (v___x_1480_ == 0)
{
lean_object* v___x_1481_; lean_object* v___x_1482_; 
lean_inc(v_binderName_1470_);
lean_dec_ref_known(v___y_1447_, 3);
v___x_1481_ = l_Lean_Expr_lam___override(v_binderName_1470_, v_a_1475_, v_a_1477_, v_binderInfo_1473_);
v___x_1482_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1431_, v_post_1433_, v___x_1481_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
return v___x_1482_;
}
else
{
size_t v___x_1483_; size_t v___x_1484_; uint8_t v___x_1485_; 
v___x_1483_ = lean_ptr_addr(v_body_1472_);
v___x_1484_ = lean_ptr_addr(v_a_1477_);
v___x_1485_ = lean_usize_dec_eq(v___x_1483_, v___x_1484_);
if (v___x_1485_ == 0)
{
lean_object* v___x_1486_; lean_object* v___x_1487_; 
lean_inc(v_binderName_1470_);
lean_dec_ref_known(v___y_1447_, 3);
v___x_1486_ = l_Lean_Expr_lam___override(v_binderName_1470_, v_a_1475_, v_a_1477_, v_binderInfo_1473_);
v___x_1487_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1431_, v_post_1433_, v___x_1486_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
return v___x_1487_;
}
else
{
uint8_t v___x_1488_; 
v___x_1488_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1473_, v_binderInfo_1473_);
if (v___x_1488_ == 0)
{
lean_object* v___x_1489_; lean_object* v___x_1490_; 
lean_inc(v_binderName_1470_);
lean_dec_ref_known(v___y_1447_, 3);
v___x_1489_ = l_Lean_Expr_lam___override(v_binderName_1470_, v_a_1475_, v_a_1477_, v_binderInfo_1473_);
v___x_1490_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1431_, v_post_1433_, v___x_1489_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
return v___x_1490_;
}
else
{
lean_object* v___x_1491_; 
lean_dec(v_a_1477_);
lean_dec(v_a_1475_);
v___x_1491_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1431_, v_post_1433_, v___y_1447_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
return v___x_1491_;
}
}
}
}
else
{
lean_dec(v_a_1475_);
lean_dec_ref_known(v___y_1447_, 3);
lean_dec_ref(v_post_1433_);
lean_dec_ref(v_pre_1431_);
return v___x_1476_;
}
}
else
{
lean_dec_ref_known(v___y_1447_, 3);
lean_dec_ref(v_post_1433_);
lean_dec_ref(v_pre_1431_);
return v___x_1474_;
}
}
case 8:
{
lean_object* v_declName_1492_; lean_object* v_type_1493_; lean_object* v_value_1494_; lean_object* v_body_1495_; uint8_t v_nondep_1496_; lean_object* v___x_1497_; 
v_declName_1492_ = lean_ctor_get(v___y_1447_, 0);
v_type_1493_ = lean_ctor_get(v___y_1447_, 1);
v_value_1494_ = lean_ctor_get(v___y_1447_, 2);
v_body_1495_ = lean_ctor_get(v___y_1447_, 3);
v_nondep_1496_ = lean_ctor_get_uint8(v___y_1447_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_1493_);
lean_inc_ref(v_post_1433_);
lean_inc_ref(v_pre_1431_);
v___x_1497_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1431_, v_post_1433_, v_type_1493_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
if (lean_obj_tag(v___x_1497_) == 0)
{
lean_object* v_a_1498_; lean_object* v___x_1499_; 
v_a_1498_ = lean_ctor_get(v___x_1497_, 0);
lean_inc(v_a_1498_);
lean_dec_ref_known(v___x_1497_, 1);
lean_inc_ref(v_value_1494_);
lean_inc_ref(v_post_1433_);
lean_inc_ref(v_pre_1431_);
v___x_1499_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1431_, v_post_1433_, v_value_1494_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
if (lean_obj_tag(v___x_1499_) == 0)
{
lean_object* v_a_1500_; lean_object* v___x_1501_; 
v_a_1500_ = lean_ctor_get(v___x_1499_, 0);
lean_inc(v_a_1500_);
lean_dec_ref_known(v___x_1499_, 1);
lean_inc_ref(v_body_1495_);
lean_inc_ref(v_post_1433_);
lean_inc_ref(v_pre_1431_);
v___x_1501_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1431_, v_post_1433_, v_body_1495_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
if (lean_obj_tag(v___x_1501_) == 0)
{
lean_object* v_a_1502_; size_t v___x_1503_; size_t v___x_1504_; uint8_t v___x_1505_; 
v_a_1502_ = lean_ctor_get(v___x_1501_, 0);
lean_inc(v_a_1502_);
lean_dec_ref_known(v___x_1501_, 1);
v___x_1503_ = lean_ptr_addr(v_type_1493_);
v___x_1504_ = lean_ptr_addr(v_a_1498_);
v___x_1505_ = lean_usize_dec_eq(v___x_1503_, v___x_1504_);
if (v___x_1505_ == 0)
{
lean_object* v___x_1506_; lean_object* v___x_1507_; 
lean_inc(v_declName_1492_);
lean_dec_ref_known(v___y_1447_, 4);
v___x_1506_ = l_Lean_Expr_letE___override(v_declName_1492_, v_a_1498_, v_a_1500_, v_a_1502_, v_nondep_1496_);
v___x_1507_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1431_, v_post_1433_, v___x_1506_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
return v___x_1507_;
}
else
{
size_t v___x_1508_; size_t v___x_1509_; uint8_t v___x_1510_; 
v___x_1508_ = lean_ptr_addr(v_value_1494_);
v___x_1509_ = lean_ptr_addr(v_a_1500_);
v___x_1510_ = lean_usize_dec_eq(v___x_1508_, v___x_1509_);
if (v___x_1510_ == 0)
{
lean_object* v___x_1511_; lean_object* v___x_1512_; 
lean_inc(v_declName_1492_);
lean_dec_ref_known(v___y_1447_, 4);
v___x_1511_ = l_Lean_Expr_letE___override(v_declName_1492_, v_a_1498_, v_a_1500_, v_a_1502_, v_nondep_1496_);
v___x_1512_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1431_, v_post_1433_, v___x_1511_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
return v___x_1512_;
}
else
{
size_t v___x_1513_; size_t v___x_1514_; uint8_t v___x_1515_; 
v___x_1513_ = lean_ptr_addr(v_body_1495_);
v___x_1514_ = lean_ptr_addr(v_a_1502_);
v___x_1515_ = lean_usize_dec_eq(v___x_1513_, v___x_1514_);
if (v___x_1515_ == 0)
{
lean_object* v___x_1516_; lean_object* v___x_1517_; 
lean_inc(v_declName_1492_);
lean_dec_ref_known(v___y_1447_, 4);
v___x_1516_ = l_Lean_Expr_letE___override(v_declName_1492_, v_a_1498_, v_a_1500_, v_a_1502_, v_nondep_1496_);
v___x_1517_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1431_, v_post_1433_, v___x_1516_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
return v___x_1517_;
}
else
{
lean_object* v___x_1518_; 
lean_dec(v_a_1502_);
lean_dec(v_a_1500_);
lean_dec(v_a_1498_);
v___x_1518_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1431_, v_post_1433_, v___y_1447_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
return v___x_1518_;
}
}
}
}
else
{
lean_dec(v_a_1500_);
lean_dec(v_a_1498_);
lean_dec_ref_known(v___y_1447_, 4);
lean_dec_ref(v_post_1433_);
lean_dec_ref(v_pre_1431_);
return v___x_1501_;
}
}
else
{
lean_dec(v_a_1498_);
lean_dec_ref_known(v___y_1447_, 4);
lean_dec_ref(v_post_1433_);
lean_dec_ref(v_pre_1431_);
return v___x_1499_;
}
}
else
{
lean_dec_ref_known(v___y_1447_, 4);
lean_dec_ref(v_post_1433_);
lean_dec_ref(v_pre_1431_);
return v___x_1497_;
}
}
case 5:
{
lean_object* v_dummy_1519_; lean_object* v_nargs_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; 
v_dummy_1519_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__1___closed__0);
v_nargs_1520_ = l_Lean_Expr_getAppNumArgs(v___y_1447_);
lean_inc(v_nargs_1520_);
v___x_1521_ = lean_mk_array(v_nargs_1520_, v_dummy_1519_);
v___x_1522_ = lean_unsigned_to_nat(1u);
v___x_1523_ = lean_nat_sub(v_nargs_1520_, v___x_1522_);
lean_dec(v_nargs_1520_);
v___x_1524_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__4(v_pre_1431_, v_post_1433_, v___y_1447_, v___x_1521_, v___x_1523_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
return v___x_1524_;
}
case 10:
{
lean_object* v_data_1525_; lean_object* v_expr_1526_; lean_object* v___x_1527_; 
v_data_1525_ = lean_ctor_get(v___y_1447_, 0);
v_expr_1526_ = lean_ctor_get(v___y_1447_, 1);
lean_inc_ref(v_expr_1526_);
lean_inc_ref(v_post_1433_);
lean_inc_ref(v_pre_1431_);
v___x_1527_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1431_, v_post_1433_, v_expr_1526_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
if (lean_obj_tag(v___x_1527_) == 0)
{
lean_object* v_a_1528_; size_t v___x_1529_; size_t v___x_1530_; uint8_t v___x_1531_; 
v_a_1528_ = lean_ctor_get(v___x_1527_, 0);
lean_inc(v_a_1528_);
lean_dec_ref_known(v___x_1527_, 1);
v___x_1529_ = lean_ptr_addr(v_expr_1526_);
v___x_1530_ = lean_ptr_addr(v_a_1528_);
v___x_1531_ = lean_usize_dec_eq(v___x_1529_, v___x_1530_);
if (v___x_1531_ == 0)
{
lean_object* v___x_1532_; lean_object* v___x_1533_; 
lean_inc(v_data_1525_);
lean_dec_ref_known(v___y_1447_, 2);
v___x_1532_ = l_Lean_Expr_mdata___override(v_data_1525_, v_a_1528_);
v___x_1533_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1431_, v_post_1433_, v___x_1532_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
return v___x_1533_;
}
else
{
lean_object* v___x_1534_; 
lean_dec(v_a_1528_);
v___x_1534_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1431_, v_post_1433_, v___y_1447_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
return v___x_1534_;
}
}
else
{
lean_dec_ref_known(v___y_1447_, 2);
lean_dec_ref(v_post_1433_);
lean_dec_ref(v_pre_1431_);
return v___x_1527_;
}
}
case 11:
{
lean_object* v_typeName_1535_; lean_object* v_idx_1536_; lean_object* v_struct_1537_; lean_object* v___x_1538_; 
v_typeName_1535_ = lean_ctor_get(v___y_1447_, 0);
v_idx_1536_ = lean_ctor_get(v___y_1447_, 1);
v_struct_1537_ = lean_ctor_get(v___y_1447_, 2);
lean_inc_ref(v_struct_1537_);
lean_inc_ref(v_post_1433_);
lean_inc_ref(v_pre_1431_);
v___x_1538_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1431_, v_post_1433_, v_struct_1537_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
if (lean_obj_tag(v___x_1538_) == 0)
{
lean_object* v_a_1539_; size_t v___x_1540_; size_t v___x_1541_; uint8_t v___x_1542_; 
v_a_1539_ = lean_ctor_get(v___x_1538_, 0);
lean_inc(v_a_1539_);
lean_dec_ref_known(v___x_1538_, 1);
v___x_1540_ = lean_ptr_addr(v_struct_1537_);
v___x_1541_ = lean_ptr_addr(v_a_1539_);
v___x_1542_ = lean_usize_dec_eq(v___x_1540_, v___x_1541_);
if (v___x_1542_ == 0)
{
lean_object* v___x_1543_; lean_object* v___x_1544_; 
lean_inc(v_idx_1536_);
lean_inc(v_typeName_1535_);
lean_dec_ref_known(v___y_1447_, 3);
v___x_1543_ = l_Lean_Expr_proj___override(v_typeName_1535_, v_idx_1536_, v_a_1539_);
v___x_1544_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1431_, v_post_1433_, v___x_1543_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
return v___x_1544_;
}
else
{
lean_object* v___x_1545_; 
lean_dec(v_a_1539_);
v___x_1545_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1431_, v_post_1433_, v___y_1447_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
return v___x_1545_;
}
}
else
{
lean_dec_ref_known(v___y_1447_, 3);
lean_dec_ref(v_post_1433_);
lean_dec_ref(v_pre_1431_);
return v___x_1538_;
}
}
default: 
{
lean_object* v___x_1546_; 
v___x_1546_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1431_, v_post_1433_, v___y_1447_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
return v___x_1546_;
}
}
}
}
}
else
{
lean_object* v_a_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1565_; 
lean_dec_ref(v_post_1433_);
lean_dec_ref(v_e_1432_);
lean_dec_ref(v_pre_1431_);
v_a_1558_ = lean_ctor_get(v___x_1441_, 0);
v_isSharedCheck_1565_ = !lean_is_exclusive(v___x_1441_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1560_ = v___x_1441_;
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_a_1558_);
lean_dec(v___x_1441_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
lean_object* v___x_1563_; 
if (v_isShared_1561_ == 0)
{
v___x_1563_ = v___x_1560_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v_a_1558_);
v___x_1563_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
return v___x_1563_;
}
}
}
}
else
{
lean_object* v_a_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1573_; 
lean_dec_ref(v_post_1433_);
lean_dec_ref(v_e_1432_);
lean_dec_ref(v_pre_1431_);
v_a_1566_ = lean_ctor_get(v___x_1440_, 0);
v_isSharedCheck_1573_ = !lean_is_exclusive(v___x_1440_);
if (v_isSharedCheck_1573_ == 0)
{
v___x_1568_ = v___x_1440_;
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_a_1566_);
lean_dec(v___x_1440_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v___x_1571_; 
if (v_isShared_1569_ == 0)
{
v___x_1571_ = v___x_1568_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v_a_1566_);
v___x_1571_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
return v___x_1571_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__1___boxed(lean_object* v___x_1574_, lean_object* v_pre_1575_, lean_object* v_e_1576_, lean_object* v_post_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_){
_start:
{
lean_object* v_res_1584_; 
v_res_1584_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__1(v___x_1574_, v_pre_1575_, v_e_1576_, v_post_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_);
lean_dec(v___y_1582_);
lean_dec_ref(v___y_1581_);
lean_dec(v___y_1580_);
lean_dec_ref(v___y_1579_);
lean_dec(v___y_1578_);
return v_res_1584_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(lean_object* v_pre_1585_, lean_object* v_post_1586_, lean_object* v_e_1587_, lean_object* v_a_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_){
_start:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; 
lean_inc(v_a_1588_);
v___x_1594_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1594_, 0, lean_box(0));
lean_closure_set(v___x_1594_, 1, lean_box(0));
lean_closure_set(v___x_1594_, 2, v_a_1588_);
v___x_1595_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__0(lean_box(0), v___x_1594_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_);
if (lean_obj_tag(v___x_1595_) == 0)
{
lean_object* v_a_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1627_; 
v_a_1596_ = lean_ctor_get(v___x_1595_, 0);
v_isSharedCheck_1627_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1598_ = v___x_1595_;
v_isShared_1599_ = v_isSharedCheck_1627_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_a_1596_);
lean_dec(v___x_1595_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1627_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v___x_1600_; 
v___x_1600_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3___redArg(v_a_1596_, v_e_1587_);
lean_dec(v_a_1596_);
if (lean_obj_tag(v___x_1600_) == 0)
{
lean_object* v___x_1601_; lean_object* v___f_1602_; lean_object* v___x_1603_; 
lean_del_object(v___x_1598_);
v___x_1601_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___closed__0));
lean_inc_ref(v_e_1587_);
v___f_1602_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__1___boxed), 10, 4);
lean_closure_set(v___f_1602_, 0, v___x_1601_);
lean_closure_set(v___f_1602_, 1, v_pre_1585_);
lean_closure_set(v___f_1602_, 2, v_e_1587_);
lean_closure_set(v___f_1602_, 3, v_post_1586_);
v___x_1603_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5___redArg(v___f_1602_, v_a_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_);
if (lean_obj_tag(v___x_1603_) == 0)
{
lean_object* v_a_1604_; lean_object* v___f_1605_; lean_object* v___x_1606_; 
v_a_1604_ = lean_ctor_get(v___x_1603_, 0);
lean_inc_n(v_a_1604_, 2);
lean_dec_ref_known(v___x_1603_, 1);
lean_inc(v_a_1588_);
v___f_1605_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1605_, 0, v_a_1588_);
lean_closure_set(v___f_1605_, 1, v_e_1587_);
lean_closure_set(v___f_1605_, 2, v_a_1604_);
v___x_1606_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__0(lean_box(0), v___f_1605_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_);
if (lean_obj_tag(v___x_1606_) == 0)
{
lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1613_; 
v_isSharedCheck_1613_ = !lean_is_exclusive(v___x_1606_);
if (v_isSharedCheck_1613_ == 0)
{
lean_object* v_unused_1614_; 
v_unused_1614_ = lean_ctor_get(v___x_1606_, 0);
lean_dec(v_unused_1614_);
v___x_1608_ = v___x_1606_;
v_isShared_1609_ = v_isSharedCheck_1613_;
goto v_resetjp_1607_;
}
else
{
lean_dec(v___x_1606_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1613_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
lean_object* v___x_1611_; 
if (v_isShared_1609_ == 0)
{
lean_ctor_set(v___x_1608_, 0, v_a_1604_);
v___x_1611_ = v___x_1608_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v_a_1604_);
v___x_1611_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
return v___x_1611_;
}
}
}
else
{
lean_object* v_a_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1622_; 
lean_dec(v_a_1604_);
v_a_1615_ = lean_ctor_get(v___x_1606_, 0);
v_isSharedCheck_1622_ = !lean_is_exclusive(v___x_1606_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1617_ = v___x_1606_;
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
else
{
lean_inc(v_a_1615_);
lean_dec(v___x_1606_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
lean_object* v___x_1620_; 
if (v_isShared_1618_ == 0)
{
v___x_1620_ = v___x_1617_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v_a_1615_);
v___x_1620_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
return v___x_1620_;
}
}
}
}
else
{
lean_dec_ref(v_e_1587_);
return v___x_1603_;
}
}
else
{
lean_object* v_val_1623_; lean_object* v___x_1625_; 
lean_dec_ref(v_e_1587_);
lean_dec_ref(v_post_1586_);
lean_dec_ref(v_pre_1585_);
v_val_1623_ = lean_ctor_get(v___x_1600_, 0);
lean_inc(v_val_1623_);
lean_dec_ref_known(v___x_1600_, 1);
if (v_isShared_1599_ == 0)
{
lean_ctor_set(v___x_1598_, 0, v_val_1623_);
v___x_1625_ = v___x_1598_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_val_1623_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
return v___x_1625_;
}
}
}
}
else
{
lean_object* v_a_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1635_; 
lean_dec_ref(v_e_1587_);
lean_dec_ref(v_post_1586_);
lean_dec_ref(v_pre_1585_);
v_a_1628_ = lean_ctor_get(v___x_1595_, 0);
v_isSharedCheck_1635_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1635_ == 0)
{
v___x_1630_ = v___x_1595_;
v_isShared_1631_ = v_isSharedCheck_1635_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_a_1628_);
lean_dec(v___x_1595_);
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
v_reuseFailAlloc_1634_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(lean_object* v_pre_1636_, lean_object* v_post_1637_, lean_object* v_e_1638_, lean_object* v_a_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_){
_start:
{
lean_object* v___x_1645_; 
lean_inc_ref(v_post_1637_);
lean_inc(v___y_1643_);
lean_inc_ref(v___y_1642_);
lean_inc(v___y_1641_);
lean_inc_ref(v___y_1640_);
lean_inc_ref(v_e_1638_);
v___x_1645_ = lean_apply_6(v_post_1637_, v_e_1638_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, lean_box(0));
if (lean_obj_tag(v___x_1645_) == 0)
{
lean_object* v_a_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1664_; 
v_a_1646_ = lean_ctor_get(v___x_1645_, 0);
v_isSharedCheck_1664_ = !lean_is_exclusive(v___x_1645_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1648_ = v___x_1645_;
v_isShared_1649_ = v_isSharedCheck_1664_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_a_1646_);
lean_dec(v___x_1645_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1664_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
switch(lean_obj_tag(v_a_1646_))
{
case 0:
{
lean_object* v_e_1650_; lean_object* v___x_1652_; 
lean_dec_ref(v_e_1638_);
lean_dec_ref(v_post_1637_);
lean_dec_ref(v_pre_1636_);
v_e_1650_ = lean_ctor_get(v_a_1646_, 0);
lean_inc_ref(v_e_1650_);
lean_dec_ref_known(v_a_1646_, 1);
if (v_isShared_1649_ == 0)
{
lean_ctor_set(v___x_1648_, 0, v_e_1650_);
v___x_1652_ = v___x_1648_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v_e_1650_);
v___x_1652_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
return v___x_1652_;
}
}
case 1:
{
lean_object* v_e_1654_; lean_object* v___x_1655_; 
lean_del_object(v___x_1648_);
lean_dec_ref(v_e_1638_);
v_e_1654_ = lean_ctor_get(v_a_1646_, 0);
lean_inc_ref(v_e_1654_);
lean_dec_ref_known(v_a_1646_, 1);
v___x_1655_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1636_, v_post_1637_, v_e_1654_, v_a_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_);
return v___x_1655_;
}
default: 
{
lean_object* v_e_x3f_1656_; 
lean_dec_ref(v_post_1637_);
lean_dec_ref(v_pre_1636_);
v_e_x3f_1656_ = lean_ctor_get(v_a_1646_, 0);
lean_inc(v_e_x3f_1656_);
lean_dec_ref_known(v_a_1646_, 1);
if (lean_obj_tag(v_e_x3f_1656_) == 0)
{
lean_object* v___x_1658_; 
if (v_isShared_1649_ == 0)
{
lean_ctor_set(v___x_1648_, 0, v_e_1638_);
v___x_1658_ = v___x_1648_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v_e_1638_);
v___x_1658_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
return v___x_1658_;
}
}
else
{
lean_object* v_val_1660_; lean_object* v___x_1662_; 
lean_dec_ref(v_e_1638_);
v_val_1660_ = lean_ctor_get(v_e_x3f_1656_, 0);
lean_inc(v_val_1660_);
lean_dec_ref_known(v_e_x3f_1656_, 1);
if (v_isShared_1649_ == 0)
{
lean_ctor_set(v___x_1648_, 0, v_val_1660_);
v___x_1662_ = v___x_1648_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v_val_1660_);
v___x_1662_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
return v___x_1662_;
}
}
}
}
}
}
else
{
lean_object* v_a_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1672_; 
lean_dec_ref(v_e_1638_);
lean_dec_ref(v_post_1637_);
lean_dec_ref(v_pre_1636_);
v_a_1665_ = lean_ctor_get(v___x_1645_, 0);
v_isSharedCheck_1672_ = !lean_is_exclusive(v___x_1645_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1667_ = v___x_1645_;
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_a_1665_);
lean_dec(v___x_1645_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_1673_, lean_object* v_post_1674_, lean_object* v_e_1675_, lean_object* v_a_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_){
_start:
{
lean_object* v_res_1682_; 
v_res_1682_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1673_, v_post_1674_, v_e_1675_, v_a_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
lean_dec(v___y_1678_);
lean_dec_ref(v___y_1677_);
lean_dec(v_a_1676_);
return v_res_1682_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_1683_, lean_object* v_post_1684_, lean_object* v_sz_1685_, lean_object* v_i_1686_, lean_object* v_bs_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_){
_start:
{
size_t v_sz_boxed_1694_; size_t v_i_boxed_1695_; lean_object* v_res_1696_; 
v_sz_boxed_1694_ = lean_unbox_usize(v_sz_1685_);
lean_dec(v_sz_1685_);
v_i_boxed_1695_ = lean_unbox_usize(v_i_1686_);
lean_dec(v_i_1686_);
v_res_1696_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__1(v_pre_1683_, v_post_1684_, v_sz_boxed_1694_, v_i_boxed_1695_, v_bs_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
lean_dec(v___y_1692_);
lean_dec_ref(v___y_1691_);
lean_dec(v___y_1690_);
lean_dec_ref(v___y_1689_);
lean_dec(v___y_1688_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__4___boxed(lean_object* v_pre_1697_, lean_object* v_post_1698_, lean_object* v_x_1699_, lean_object* v_x_1700_, lean_object* v_x_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_){
_start:
{
lean_object* v_res_1708_; 
v_res_1708_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__4(v_pre_1697_, v_post_1698_, v_x_1699_, v_x_1700_, v_x_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_);
lean_dec(v___y_1706_);
lean_dec_ref(v___y_1705_);
lean_dec(v___y_1704_);
lean_dec_ref(v___y_1703_);
lean_dec(v___y_1702_);
return v_res_1708_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___boxed(lean_object* v_pre_1709_, lean_object* v_post_1710_, lean_object* v_e_1711_, lean_object* v_a_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_){
_start:
{
lean_object* v_res_1718_; 
v_res_1718_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1709_, v_post_1710_, v_e_1711_, v_a_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
lean_dec(v___y_1714_);
lean_dec_ref(v___y_1713_);
lean_dec(v_a_1712_);
return v_res_1718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___lam__0(lean_object* v_00_u03b1_1719_, lean_object* v_x_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_){
_start:
{
lean_object* v___x_1726_; lean_object* v___x_1727_; 
v___x_1726_ = lean_apply_1(v_x_1720_, lean_box(0));
v___x_1727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1727_, 0, v___x_1726_);
return v___x_1727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___lam__0___boxed(lean_object* v_00_u03b1_1728_, lean_object* v_x_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_){
_start:
{
lean_object* v_res_1735_; 
v_res_1735_ = l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___lam__0(v_00_u03b1_1728_, v_x_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
lean_dec(v___y_1733_);
lean_dec_ref(v___y_1732_);
lean_dec(v___y_1731_);
lean_dec_ref(v___y_1730_);
return v_res_1735_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; 
v___x_1736_ = lean_box(0);
v___x_1737_ = lean_unsigned_to_nat(16u);
v___x_1738_ = lean_mk_array(v___x_1737_, v___x_1736_);
return v___x_1738_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; 
v___x_1739_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__0, &l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__0_once, _init_l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__0);
v___x_1740_ = lean_unsigned_to_nat(0u);
v___x_1741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1741_, 0, v___x_1740_);
lean_ctor_set(v___x_1741_, 1, v___x_1739_);
return v___x_1741_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1742_; lean_object* v___x_1743_; 
v___x_1742_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__1, &l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__1_once, _init_l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__1);
v___x_1743_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1743_, 0, lean_box(0));
lean_closure_set(v___x_1743_, 1, lean_box(0));
lean_closure_set(v___x_1743_, 2, v___x_1742_);
return v___x_1743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0(lean_object* v_input_1744_, lean_object* v_pre_1745_, lean_object* v_post_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_){
_start:
{
lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v_a_1754_; lean_object* v___x_1755_; 
v___x_1752_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__2, &l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__2_once, _init_l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__2);
v___x_1753_ = l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___lam__0(lean_box(0), v___x_1752_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
v_a_1754_ = lean_ctor_get(v___x_1753_, 0);
lean_inc(v_a_1754_);
lean_dec_ref(v___x_1753_);
v___x_1755_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1745_, v_post_1746_, v_input_1744_, v_a_1754_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
if (lean_obj_tag(v___x_1755_) == 0)
{
lean_object* v_a_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1765_; 
v_a_1756_ = lean_ctor_get(v___x_1755_, 0);
lean_inc(v_a_1756_);
lean_dec_ref_known(v___x_1755_, 1);
v___x_1757_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1757_, 0, lean_box(0));
lean_closure_set(v___x_1757_, 1, lean_box(0));
lean_closure_set(v___x_1757_, 2, v_a_1754_);
v___x_1758_ = l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___lam__0(lean_box(0), v___x_1757_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
v_isSharedCheck_1765_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1765_ == 0)
{
lean_object* v_unused_1766_; 
v_unused_1766_ = lean_ctor_get(v___x_1758_, 0);
lean_dec(v_unused_1766_);
v___x_1760_ = v___x_1758_;
v_isShared_1761_ = v_isSharedCheck_1765_;
goto v_resetjp_1759_;
}
else
{
lean_dec(v___x_1758_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1765_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v___x_1763_; 
if (v_isShared_1761_ == 0)
{
lean_ctor_set(v___x_1760_, 0, v_a_1756_);
v___x_1763_ = v___x_1760_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v_a_1756_);
v___x_1763_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
return v___x_1763_;
}
}
}
else
{
lean_dec(v_a_1754_);
return v___x_1755_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___boxed(lean_object* v_input_1767_, lean_object* v_pre_1768_, lean_object* v_post_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_){
_start:
{
lean_object* v_res_1775_; 
v_res_1775_ = l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0(v_input_1767_, v_pre_1768_, v_post_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_);
lean_dec(v___y_1773_);
lean_dec_ref(v___y_1772_);
lean_dec(v___y_1771_);
lean_dec_ref(v___y_1770_);
return v_res_1775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_reduceProjs(lean_object* v_e_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_){
_start:
{
lean_object* v___f_1784_; lean_object* v___f_1785_; lean_object* v___x_1786_; 
v___f_1784_ = ((lean_object*)(l_Lean_Meta_PProdN_reduceProjs___closed__0));
v___f_1785_ = ((lean_object*)(l_Lean_Meta_PProdN_reduceProjs___closed__1));
v___x_1786_ = l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0(v_e_1778_, v___f_1784_, v___f_1785_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_);
return v___x_1786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_reduceProjs___boxed(lean_object* v_e_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_){
_start:
{
lean_object* v_res_1793_; 
v_res_1793_ = l_Lean_Meta_PProdN_reduceProjs(v_e_1787_, v_a_1788_, v_a_1789_, v_a_1790_, v_a_1791_);
lean_dec(v_a_1791_);
lean_dec_ref(v_a_1790_);
lean_dec(v_a_1789_);
lean_dec_ref(v_a_1788_);
return v_res_1793_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_1794_, lean_object* v_m_1795_, lean_object* v_a_1796_){
_start:
{
lean_object* v___x_1797_; 
v___x_1797_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3___redArg(v_m_1795_, v_a_1796_);
return v___x_1797_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_1798_, lean_object* v_m_1799_, lean_object* v_a_1800_){
_start:
{
lean_object* v_res_1801_; 
v_res_1801_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3(v_00_u03b2_1798_, v_m_1799_, v_a_1800_);
lean_dec_ref(v_a_1800_);
lean_dec_ref(v_m_1799_);
return v_res_1801_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_1802_, lean_object* v_ref_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_){
_start:
{
lean_object* v___x_1807_; 
v___x_1807_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_1803_);
return v___x_1807_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1808_, lean_object* v_ref_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_){
_start:
{
lean_object* v_res_1813_; 
v_res_1813_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_1808_, v_ref_1809_, v___y_1810_, v___y_1811_);
lean_dec(v___y_1811_);
lean_dec_ref(v___y_1810_);
return v_res_1813_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__8(lean_object* v_00_u03b1_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_){
_start:
{
lean_object* v___x_1818_; 
v___x_1818_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__8___redArg();
return v___x_1818_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__8___boxed(lean_object* v_00_u03b1_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_){
_start:
{
lean_object* v_res_1823_; 
v_res_1823_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__8(v_00_u03b1_1819_, v___y_1820_, v___y_1821_);
lean_dec(v___y_1821_);
lean_dec_ref(v___y_1820_);
return v_res_1823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5(lean_object* v_00_u03b1_1824_, lean_object* v_x_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_){
_start:
{
lean_object* v___x_1832_; 
v___x_1832_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5___redArg(v_x_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_);
return v___x_1832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b1_1833_, lean_object* v_x_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_){
_start:
{
lean_object* v_res_1841_; 
v_res_1841_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5(v_00_u03b1_1833_, v_x_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_);
lean_dec(v___y_1839_);
lean_dec_ref(v___y_1838_);
lean_dec(v___y_1837_);
lean_dec_ref(v___y_1836_);
lean_dec(v___y_1835_);
return v_res_1841_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6(lean_object* v_00_u03b2_1842_, lean_object* v_m_1843_, lean_object* v_a_1844_, lean_object* v_b_1845_){
_start:
{
lean_object* v___x_1846_; 
v___x_1846_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6___redArg(v_m_1843_, v_a_1844_, v_b_1845_);
return v___x_1846_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b2_1847_, lean_object* v_a_1848_, lean_object* v_x_1849_){
_start:
{
lean_object* v___x_1850_; 
v___x_1850_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3_spec__4___redArg(v_a_1848_, v_x_1849_);
return v___x_1850_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3_spec__4___boxed(lean_object* v_00_u03b2_1851_, lean_object* v_a_1852_, lean_object* v_x_1853_){
_start:
{
lean_object* v_res_1854_; 
v_res_1854_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3_spec__4(v_00_u03b2_1851_, v_a_1852_, v_x_1853_);
lean_dec(v_x_1853_);
lean_dec_ref(v_a_1852_);
return v_res_1854_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__10(lean_object* v_00_u03b2_1855_, lean_object* v_a_1856_, lean_object* v_x_1857_){
_start:
{
uint8_t v___x_1858_; 
v___x_1858_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__10___redArg(v_a_1856_, v_x_1857_);
return v___x_1858_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__10___boxed(lean_object* v_00_u03b2_1859_, lean_object* v_a_1860_, lean_object* v_x_1861_){
_start:
{
uint8_t v_res_1862_; lean_object* v_r_1863_; 
v_res_1862_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__10(v_00_u03b2_1859_, v_a_1860_, v_x_1861_);
lean_dec(v_x_1861_);
lean_dec_ref(v_a_1860_);
v_r_1863_ = lean_box(v_res_1862_);
return v_r_1863_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11(lean_object* v_00_u03b2_1864_, lean_object* v_data_1865_){
_start:
{
lean_object* v___x_1866_; 
v___x_1866_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11___redArg(v_data_1865_);
return v___x_1866_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__12(lean_object* v_00_u03b2_1867_, lean_object* v_a_1868_, lean_object* v_b_1869_, lean_object* v_x_1870_){
_start:
{
lean_object* v___x_1871_; 
v___x_1871_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__12___redArg(v_a_1868_, v_b_1869_, v_x_1870_);
return v___x_1871_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11_spec__12(lean_object* v_00_u03b2_1872_, lean_object* v_i_1873_, lean_object* v_source_1874_, lean_object* v_target_1875_){
_start:
{
lean_object* v___x_1876_; 
v___x_1876_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v_i_1873_, v_source_1874_, v_target_1875_);
return v___x_1876_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13(lean_object* v_00_u03b2_1877_, lean_object* v_x_1878_, lean_object* v_x_1879_){
_start:
{
lean_object* v___x_1880_; 
v___x_1880_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_x_1878_, v_x_1879_);
return v___x_1880_;
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
