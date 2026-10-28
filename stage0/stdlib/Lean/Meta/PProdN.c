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
lean_object* lean_expr_dbg_to_string(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isSort(lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Expr_sortLevel_x21(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_mkPProdFst___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkPProdFstM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkPProdFstM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_PProdN_0__Lean_Meta_mkTypeSnd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "_private.Lean.Meta.PProdN.0.Lean.Meta.mkTypeSnd"};
static const lean_object* l___private_Lean_Meta_PProdN_0__Lean_Meta_mkTypeSnd___closed__0 = (const lean_object*)&l___private_Lean_Meta_PProdN_0__Lean_Meta_mkTypeSnd___closed__0_value;
static const lean_string_object l___private_Lean_Meta_PProdN_0__Lean_Meta_mkTypeSnd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "mkTypeSnd: cannot handle type "};
static const lean_object* l___private_Lean_Meta_PProdN_0__Lean_Meta_mkTypeSnd___closed__1 = (const lean_object*)&l___private_Lean_Meta_PProdN_0__Lean_Meta_mkTypeSnd___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_PProdN_0__Lean_Meta_mkTypeSnd(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_PProdN_0__Lean_Meta_mkTypeSnd___boxed(lean_object*);
static const lean_string_object l_Lean_Meta_mkPProdSnd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.Meta.mkPProdSnd"};
static const lean_object* l_Lean_Meta_mkPProdSnd___closed__0 = (const lean_object*)&l_Lean_Meta_mkPProdSnd___closed__0_value;
static const lean_string_object l_Lean_Meta_mkPProdSnd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "mkPProdSnd: cannot handle "};
static const lean_object* l_Lean_Meta_mkPProdSnd___closed__1 = (const lean_object*)&l_Lean_Meta_mkPProdSnd___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkPProdSnd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkPProdSnd___boxed(lean_object*, lean_object*);
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
lean_dec_ref(v___x_168_);
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
lean_dec_ref(v___x_170_);
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
v___x_177_ = lean_unsigned_to_nat(0u);
v___x_178_ = l_Lean_Expr_proj___override(v___x_175_, v___x_177_, v_e_153_);
return v___x_178_;
}
}
else
{
lean_object* v___x_179_; lean_object* v___x_180_; 
lean_dec_ref(v___x_172_);
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
v___x_165_ = lean_string_append(v___x_163_, v___x_164_);
lean_dec_ref(v___x_164_);
v___x_166_ = l_mkPanicMessageWithDecl(v___x_155_, v___x_156_, v___x_157_, v___x_158_, v___x_165_);
lean_dec_ref(v___x_165_);
v___x_167_ = l_panic___at___00Lean_Meta_mkPProdFst_spec__0(v___x_166_);
return v___x_167_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPProdFst___boxed(lean_object* v_t_181_, lean_object* v_e_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l_Lean_Meta_mkPProdFst(v_t_181_, v_e_182_);
lean_dec_ref(v_t_181_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPProdFstM(lean_object* v_e_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_){
_start:
{
lean_object* v___x_190_; 
lean_inc(v_a_188_);
lean_inc_ref(v_a_187_);
lean_inc(v_a_186_);
lean_inc_ref(v_a_185_);
lean_inc_ref(v_e_184_);
v___x_190_ = lean_infer_type(v_e_184_, v_a_185_, v_a_186_, v_a_187_, v_a_188_);
if (lean_obj_tag(v___x_190_) == 0)
{
lean_object* v_a_191_; lean_object* v___x_192_; 
v_a_191_ = lean_ctor_get(v___x_190_, 0);
lean_inc(v_a_191_);
lean_dec_ref_known(v___x_190_, 1);
lean_inc(v_a_188_);
lean_inc_ref(v_a_187_);
lean_inc(v_a_186_);
lean_inc_ref(v_a_185_);
v___x_192_ = lean_whnf(v_a_191_, v_a_185_, v_a_186_, v_a_187_, v_a_188_);
if (lean_obj_tag(v___x_192_) == 0)
{
lean_object* v_a_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_201_; 
v_a_193_ = lean_ctor_get(v___x_192_, 0);
v_isSharedCheck_201_ = !lean_is_exclusive(v___x_192_);
if (v_isSharedCheck_201_ == 0)
{
v___x_195_ = v___x_192_;
v_isShared_196_ = v_isSharedCheck_201_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_a_193_);
lean_dec(v___x_192_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_201_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v___x_197_; lean_object* v___x_199_; 
v___x_197_ = l_Lean_Meta_mkPProdFst(v_a_193_, v_e_184_);
lean_dec(v_a_193_);
if (v_isShared_196_ == 0)
{
lean_ctor_set(v___x_195_, 0, v___x_197_);
v___x_199_ = v___x_195_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v___x_197_);
v___x_199_ = v_reuseFailAlloc_200_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
return v___x_199_;
}
}
}
else
{
lean_dec_ref(v_e_184_);
return v___x_192_;
}
}
else
{
lean_dec_ref(v_e_184_);
return v___x_190_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPProdFstM___boxed(lean_object* v_e_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_Lean_Meta_mkPProdFstM(v_e_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_);
lean_dec(v_a_206_);
lean_dec_ref(v_a_205_);
lean_dec(v_a_204_);
lean_dec_ref(v_a_203_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PProdN_0__Lean_Meta_mkTypeSnd(lean_object* v_t_211_){
_start:
{
lean_object* v___x_222_; uint8_t v___x_223_; 
v___x_222_ = l_Lean_Expr_cleanupAnnotations(v_t_211_);
v___x_223_ = l_Lean_Expr_isApp(v___x_222_);
if (v___x_223_ == 0)
{
lean_dec_ref(v___x_222_);
goto v___jp_212_;
}
else
{
lean_object* v___x_224_; uint8_t v___x_225_; 
v___x_224_ = l_Lean_Expr_appFnCleanup___redArg(v___x_222_);
v___x_225_ = l_Lean_Expr_isApp(v___x_224_);
if (v___x_225_ == 0)
{
lean_dec_ref(v___x_224_);
lean_dec_ref(v___x_222_);
goto v___jp_212_;
}
else
{
lean_object* v_arg_226_; lean_object* v___x_227_; lean_object* v___x_228_; uint8_t v___x_229_; 
v_arg_226_ = lean_ctor_get(v___x_222_, 1);
lean_inc_ref(v_arg_226_);
lean_dec_ref(v___x_222_);
v___x_227_ = l_Lean_Expr_appFnCleanup___redArg(v___x_224_);
lean_dec_ref(v___x_224_);
v___x_228_ = ((lean_object*)(l_Lean_Meta_mkPProd___closed__3));
v___x_229_ = l_Lean_Expr_isConstOf(v___x_227_, v___x_228_);
if (v___x_229_ == 0)
{
lean_object* v___x_230_; uint8_t v___x_231_; 
v___x_230_ = ((lean_object*)(l_Lean_Meta_mkPProd___closed__1));
v___x_231_ = l_Lean_Expr_isConstOf(v___x_227_, v___x_230_);
lean_dec_ref(v___x_227_);
if (v___x_231_ == 0)
{
lean_dec_ref(v_arg_226_);
goto v___jp_212_;
}
else
{
return v_arg_226_;
}
}
else
{
lean_dec_ref(v___x_227_);
return v_arg_226_;
}
}
}
v___jp_212_:
{
lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_213_ = ((lean_object*)(l_Lean_Meta_mkPProdFst___closed__0));
v___x_214_ = ((lean_object*)(l___private_Lean_Meta_PProdN_0__Lean_Meta_mkTypeSnd___closed__0));
v___x_215_ = lean_unsigned_to_nat(70u);
v___x_216_ = lean_unsigned_to_nat(9u);
v___x_217_ = ((lean_object*)(l___private_Lean_Meta_PProdN_0__Lean_Meta_mkTypeSnd___closed__1));
v___x_218_ = lean_expr_dbg_to_string(v_t_211_);
v___x_219_ = lean_string_append(v___x_217_, v___x_218_);
lean_dec_ref(v___x_218_);
v___x_220_ = l_mkPanicMessageWithDecl(v___x_213_, v___x_214_, v___x_215_, v___x_216_, v___x_219_);
lean_dec_ref(v___x_219_);
v___x_221_ = l_panic___at___00Lean_Meta_mkPProdFst_spec__0(v___x_220_);
return v___x_221_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PProdN_0__Lean_Meta_mkTypeSnd___boxed(lean_object* v_t_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_mkTypeSnd(v_t_232_);
lean_dec_ref(v_t_232_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPProdSnd(lean_object* v_t_236_, lean_object* v_e_237_){
_start:
{
lean_object* v___x_252_; uint8_t v___x_253_; 
v___x_252_ = l_Lean_Expr_cleanupAnnotations(v_t_236_);
v___x_253_ = l_Lean_Expr_isApp(v___x_252_);
if (v___x_253_ == 0)
{
lean_dec_ref(v___x_252_);
goto v___jp_238_;
}
else
{
lean_object* v___x_254_; uint8_t v___x_255_; 
v___x_254_ = l_Lean_Expr_appFnCleanup___redArg(v___x_252_);
lean_dec_ref(v___x_252_);
v___x_255_ = l_Lean_Expr_isApp(v___x_254_);
if (v___x_255_ == 0)
{
lean_dec_ref(v___x_254_);
goto v___jp_238_;
}
else
{
lean_object* v___x_256_; lean_object* v___x_257_; uint8_t v___x_258_; 
v___x_256_ = l_Lean_Expr_appFnCleanup___redArg(v___x_254_);
lean_dec_ref(v___x_254_);
v___x_257_ = ((lean_object*)(l_Lean_Meta_mkPProd___closed__3));
v___x_258_ = l_Lean_Expr_isConstOf(v___x_256_, v___x_257_);
if (v___x_258_ == 0)
{
lean_object* v___x_259_; uint8_t v___x_260_; 
v___x_259_ = ((lean_object*)(l_Lean_Meta_mkPProd___closed__1));
v___x_260_ = l_Lean_Expr_isConstOf(v___x_256_, v___x_259_);
lean_dec_ref(v___x_256_);
if (v___x_260_ == 0)
{
goto v___jp_238_;
}
else
{
lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_261_ = lean_unsigned_to_nat(1u);
v___x_262_ = l_Lean_Expr_proj___override(v___x_259_, v___x_261_, v_e_237_);
return v___x_262_;
}
}
else
{
lean_object* v___x_263_; lean_object* v___x_264_; 
lean_dec_ref(v___x_256_);
v___x_263_ = lean_unsigned_to_nat(1u);
v___x_264_ = l_Lean_Expr_proj___override(v___x_257_, v___x_263_, v_e_237_);
return v___x_264_;
}
}
}
v___jp_238_:
{
lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_239_ = ((lean_object*)(l_Lean_Meta_mkPProdFst___closed__0));
v___x_240_ = ((lean_object*)(l_Lean_Meta_mkPProdSnd___closed__0));
v___x_241_ = lean_unsigned_to_nat(77u);
v___x_242_ = lean_unsigned_to_nat(9u);
v___x_243_ = ((lean_object*)(l_Lean_Meta_mkPProdSnd___closed__1));
v___x_244_ = lean_expr_dbg_to_string(v_e_237_);
lean_dec_ref(v_e_237_);
v___x_245_ = lean_string_append(v___x_243_, v___x_244_);
lean_dec_ref(v___x_244_);
v___x_246_ = ((lean_object*)(l_Lean_Meta_mkPProdFst___closed__3));
v___x_247_ = lean_string_append(v___x_245_, v___x_246_);
v___x_248_ = lean_expr_dbg_to_string(v_t_236_);
v___x_249_ = lean_string_append(v___x_247_, v___x_248_);
lean_dec_ref(v___x_248_);
v___x_250_ = l_mkPanicMessageWithDecl(v___x_239_, v___x_240_, v___x_241_, v___x_242_, v___x_249_);
lean_dec_ref(v___x_249_);
v___x_251_ = l_panic___at___00Lean_Meta_mkPProdFst_spec__0(v___x_250_);
return v___x_251_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPProdSnd___boxed(lean_object* v_t_265_, lean_object* v_e_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l_Lean_Meta_mkPProdSnd(v_t_265_, v_e_266_);
lean_dec_ref(v_t_265_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPProdSndM(lean_object* v_e_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_){
_start:
{
lean_object* v___x_274_; 
lean_inc(v_a_272_);
lean_inc_ref(v_a_271_);
lean_inc(v_a_270_);
lean_inc_ref(v_a_269_);
lean_inc_ref(v_e_268_);
v___x_274_ = lean_infer_type(v_e_268_, v_a_269_, v_a_270_, v_a_271_, v_a_272_);
if (lean_obj_tag(v___x_274_) == 0)
{
lean_object* v_a_275_; lean_object* v___x_276_; 
v_a_275_ = lean_ctor_get(v___x_274_, 0);
lean_inc(v_a_275_);
lean_dec_ref_known(v___x_274_, 1);
lean_inc(v_a_272_);
lean_inc_ref(v_a_271_);
lean_inc(v_a_270_);
lean_inc_ref(v_a_269_);
v___x_276_ = lean_whnf(v_a_275_, v_a_269_, v_a_270_, v_a_271_, v_a_272_);
if (lean_obj_tag(v___x_276_) == 0)
{
lean_object* v_a_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_285_; 
v_a_277_ = lean_ctor_get(v___x_276_, 0);
v_isSharedCheck_285_ = !lean_is_exclusive(v___x_276_);
if (v_isSharedCheck_285_ == 0)
{
v___x_279_ = v___x_276_;
v_isShared_280_ = v_isSharedCheck_285_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_a_277_);
lean_dec(v___x_276_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_285_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v___x_281_; lean_object* v___x_283_; 
v___x_281_ = l_Lean_Meta_mkPProdSnd(v_a_277_, v_e_268_);
lean_dec(v_a_277_);
if (v_isShared_280_ == 0)
{
lean_ctor_set(v___x_279_, 0, v___x_281_);
v___x_283_ = v___x_279_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v___x_281_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
}
}
}
else
{
lean_dec_ref(v_e_268_);
return v___x_276_;
}
}
else
{
lean_dec_ref(v_e_268_);
return v___x_274_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPProdSndM___boxed(lean_object* v_e_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_Lean_Meta_mkPProdSndM(v_e_286_, v_a_287_, v_a_288_, v_a_289_, v_a_290_);
lean_dec(v_a_290_);
lean_dec_ref(v_a_289_);
lean_dec(v_a_288_);
lean_dec_ref(v_a_287_);
return v_res_292_;
}
}
static lean_object* _init_l_Lean_Meta_PProdN_genMk___redArg___closed__0(void){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = l_instMonadEIO___redArg();
return v___x_293_;
}
}
static lean_object* _init_l_Lean_Meta_PProdN_genMk___redArg___closed__1(void){
_start:
{
lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_294_ = lean_obj_once(&l_Lean_Meta_PProdN_genMk___redArg___closed__0, &l_Lean_Meta_PProdN_genMk___redArg___closed__0_once, _init_l_Lean_Meta_PProdN_genMk___redArg___closed__0);
v___x_295_ = l_StateRefT_x27_instMonad___redArg(v___x_294_);
return v___x_295_;
}
}
static lean_object* _init_l_Lean_Meta_PProdN_genMk___redArg___closed__9(void){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_303_ = ((lean_object*)(l_Lean_Meta_PProdN_genMk___redArg___closed__8));
v___x_304_ = lean_unsigned_to_nat(2u);
v___x_305_ = lean_unsigned_to_nat(90u);
v___x_306_ = ((lean_object*)(l_Lean_Meta_PProdN_genMk___redArg___closed__7));
v___x_307_ = ((lean_object*)(l_Lean_Meta_mkPProdFst___closed__0));
v___x_308_ = l_mkPanicMessageWithDecl(v___x_307_, v___x_306_, v___x_305_, v___x_304_, v___x_303_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_genMk___redArg(lean_object* v_inst_309_, lean_object* v_mk_310_, lean_object* v_xs_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_){
_start:
{
lean_object* v___x_317_; lean_object* v_toApplicative_318_; lean_object* v_toFunctor_319_; lean_object* v_toSeq_320_; lean_object* v_toSeqLeft_321_; lean_object* v_toSeqRight_322_; lean_object* v___f_323_; lean_object* v___f_324_; lean_object* v___f_325_; lean_object* v___f_326_; lean_object* v___x_327_; lean_object* v___f_328_; lean_object* v___f_329_; lean_object* v___f_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v_toApplicative_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_379_; 
v___x_317_ = lean_obj_once(&l_Lean_Meta_PProdN_genMk___redArg___closed__1, &l_Lean_Meta_PProdN_genMk___redArg___closed__1_once, _init_l_Lean_Meta_PProdN_genMk___redArg___closed__1);
v_toApplicative_318_ = lean_ctor_get(v___x_317_, 0);
v_toFunctor_319_ = lean_ctor_get(v_toApplicative_318_, 0);
v_toSeq_320_ = lean_ctor_get(v_toApplicative_318_, 2);
v_toSeqLeft_321_ = lean_ctor_get(v_toApplicative_318_, 3);
v_toSeqRight_322_ = lean_ctor_get(v_toApplicative_318_, 4);
v___f_323_ = ((lean_object*)(l_Lean_Meta_PProdN_genMk___redArg___closed__2));
v___f_324_ = ((lean_object*)(l_Lean_Meta_PProdN_genMk___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_319_, 2);
v___f_325_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_325_, 0, v_toFunctor_319_);
v___f_326_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_326_, 0, v_toFunctor_319_);
v___x_327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_327_, 0, v___f_325_);
lean_ctor_set(v___x_327_, 1, v___f_326_);
lean_inc(v_toSeqRight_322_);
v___f_328_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_328_, 0, v_toSeqRight_322_);
lean_inc(v_toSeqLeft_321_);
v___f_329_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_329_, 0, v_toSeqLeft_321_);
lean_inc(v_toSeq_320_);
v___f_330_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_330_, 0, v_toSeq_320_);
v___x_331_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_331_, 0, v___x_327_);
lean_ctor_set(v___x_331_, 1, v___f_323_);
lean_ctor_set(v___x_331_, 2, v___f_330_);
lean_ctor_set(v___x_331_, 3, v___f_329_);
lean_ctor_set(v___x_331_, 4, v___f_328_);
v___x_332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_332_, 0, v___x_331_);
lean_ctor_set(v___x_332_, 1, v___f_324_);
v___x_333_ = l_StateRefT_x27_instMonad___redArg(v___x_332_);
v_toApplicative_334_ = lean_ctor_get(v___x_333_, 0);
v_isSharedCheck_379_ = !lean_is_exclusive(v___x_333_);
if (v_isSharedCheck_379_ == 0)
{
lean_object* v_unused_380_; 
v_unused_380_ = lean_ctor_get(v___x_333_, 1);
lean_dec(v_unused_380_);
v___x_336_ = v___x_333_;
v_isShared_337_ = v_isSharedCheck_379_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_toApplicative_334_);
lean_dec(v___x_333_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_379_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v_toFunctor_338_; lean_object* v_toSeq_339_; lean_object* v_toSeqLeft_340_; lean_object* v_toSeqRight_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_377_; 
v_toFunctor_338_ = lean_ctor_get(v_toApplicative_334_, 0);
v_toSeq_339_ = lean_ctor_get(v_toApplicative_334_, 2);
v_toSeqLeft_340_ = lean_ctor_get(v_toApplicative_334_, 3);
v_toSeqRight_341_ = lean_ctor_get(v_toApplicative_334_, 4);
v_isSharedCheck_377_ = !lean_is_exclusive(v_toApplicative_334_);
if (v_isSharedCheck_377_ == 0)
{
lean_object* v_unused_378_; 
v_unused_378_ = lean_ctor_get(v_toApplicative_334_, 1);
lean_dec(v_unused_378_);
v___x_343_ = v_toApplicative_334_;
v_isShared_344_ = v_isSharedCheck_377_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_toSeqRight_341_);
lean_inc(v_toSeqLeft_340_);
lean_inc(v_toSeq_339_);
lean_inc(v_toFunctor_338_);
lean_dec(v_toApplicative_334_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_377_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v___f_345_; lean_object* v___f_346_; lean_object* v___f_347_; lean_object* v___f_348_; lean_object* v___x_349_; lean_object* v___f_350_; lean_object* v___f_351_; lean_object* v___f_352_; lean_object* v___x_354_; 
v___f_345_ = ((lean_object*)(l_Lean_Meta_PProdN_genMk___redArg___closed__4));
v___f_346_ = ((lean_object*)(l_Lean_Meta_PProdN_genMk___redArg___closed__5));
lean_inc_ref(v_toFunctor_338_);
v___f_347_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_347_, 0, v_toFunctor_338_);
v___f_348_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_348_, 0, v_toFunctor_338_);
v___x_349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_349_, 0, v___f_347_);
lean_ctor_set(v___x_349_, 1, v___f_348_);
v___f_350_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_350_, 0, v_toSeqRight_341_);
v___f_351_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_351_, 0, v_toSeqLeft_340_);
v___f_352_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_352_, 0, v_toSeq_339_);
if (v_isShared_344_ == 0)
{
lean_ctor_set(v___x_343_, 4, v___f_350_);
lean_ctor_set(v___x_343_, 3, v___f_351_);
lean_ctor_set(v___x_343_, 2, v___f_352_);
lean_ctor_set(v___x_343_, 1, v___f_345_);
lean_ctor_set(v___x_343_, 0, v___x_349_);
v___x_354_ = v___x_343_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v___x_349_);
lean_ctor_set(v_reuseFailAlloc_376_, 1, v___f_345_);
lean_ctor_set(v_reuseFailAlloc_376_, 2, v___f_352_);
lean_ctor_set(v_reuseFailAlloc_376_, 3, v___f_351_);
lean_ctor_set(v_reuseFailAlloc_376_, 4, v___f_350_);
v___x_354_ = v_reuseFailAlloc_376_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
lean_object* v___x_356_; 
if (v_isShared_337_ == 0)
{
lean_ctor_set(v___x_336_, 1, v___f_346_);
lean_ctor_set(v___x_336_, 0, v___x_354_);
v___x_356_ = v___x_336_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v___x_354_);
lean_ctor_set(v_reuseFailAlloc_375_, 1, v___f_346_);
v___x_356_ = v_reuseFailAlloc_375_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
lean_object* v___x_357_; lean_object* v___x_358_; uint8_t v___x_359_; 
v___x_357_ = lean_array_get_size(v_xs_311_);
v___x_358_ = lean_unsigned_to_nat(0u);
v___x_359_ = lean_nat_dec_eq(v___x_357_, v___x_358_);
if (v___x_359_ == 0)
{
lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; uint8_t v___x_365_; 
v___x_360_ = lean_unsigned_to_nat(1u);
v___x_361_ = lean_nat_sub(v___x_357_, v___x_360_);
v___x_362_ = lean_array_get(v_inst_309_, v_xs_311_, v___x_361_);
lean_dec(v___x_361_);
v___x_363_ = lean_array_pop(v_xs_311_);
v___x_364_ = lean_array_get_size(v___x_363_);
v___x_365_ = lean_nat_dec_lt(v___x_358_, v___x_364_);
if (v___x_365_ == 0)
{
lean_object* v___x_366_; 
lean_dec_ref(v___x_363_);
lean_dec_ref(v___x_356_);
lean_dec_ref(v_mk_310_);
v___x_366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_366_, 0, v___x_362_);
return v___x_366_;
}
else
{
size_t v___x_367_; size_t v___x_368_; lean_object* v___x_271__overap_369_; lean_object* v___x_370_; 
v___x_367_ = lean_usize_of_nat(v___x_364_);
v___x_368_ = ((size_t)0ULL);
v___x_271__overap_369_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_356_, v_mk_310_, v___x_363_, v___x_367_, v___x_368_, v___x_362_);
lean_inc(v_a_315_);
lean_inc_ref(v_a_314_);
lean_inc(v_a_313_);
lean_inc_ref(v_a_312_);
v___x_370_ = lean_apply_5(v___x_271__overap_369_, v_a_312_, v_a_313_, v_a_314_, v_a_315_, lean_box(0));
return v___x_370_;
}
}
else
{
lean_object* v___f_371_; lean_object* v___x_372_; lean_object* v___x_316__overap_373_; lean_object* v___x_374_; 
lean_dec_ref(v___x_356_);
lean_dec_ref(v_xs_311_);
lean_dec_ref(v_mk_310_);
v___f_371_ = ((lean_object*)(l_Lean_Meta_PProdN_genMk___redArg___closed__6));
v___x_372_ = lean_obj_once(&l_Lean_Meta_PProdN_genMk___redArg___closed__9, &l_Lean_Meta_PProdN_genMk___redArg___closed__9_once, _init_l_Lean_Meta_PProdN_genMk___redArg___closed__9);
v___x_316__overap_373_ = l_panic___redArg(v___f_371_, v___x_372_);
lean_inc(v_a_315_);
lean_inc_ref(v_a_314_);
lean_inc(v_a_313_);
lean_inc_ref(v_a_312_);
v___x_374_ = lean_apply_5(v___x_316__overap_373_, v_a_312_, v_a_313_, v_a_314_, v_a_315_, lean_box(0));
return v___x_374_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_genMk___redArg___boxed(lean_object* v_inst_381_, lean_object* v_mk_382_, lean_object* v_xs_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Lean_Meta_PProdN_genMk___redArg(v_inst_381_, v_mk_382_, v_xs_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_);
lean_dec(v_a_387_);
lean_dec_ref(v_a_386_);
lean_dec(v_a_385_);
lean_dec_ref(v_a_384_);
lean_dec(v_inst_381_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_genMk(lean_object* v_00_u03b1_390_, lean_object* v_inst_391_, lean_object* v_mk_392_, lean_object* v_xs_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_){
_start:
{
lean_object* v___x_399_; 
v___x_399_ = l_Lean_Meta_PProdN_genMk___redArg(v_inst_391_, v_mk_392_, v_xs_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_genMk___boxed(lean_object* v_00_u03b1_400_, lean_object* v_inst_401_, lean_object* v_mk_402_, lean_object* v_xs_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_Lean_Meta_PProdN_genMk(v_00_u03b1_400_, v_inst_401_, v_mk_402_, v_xs_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_);
lean_dec(v_a_407_);
lean_dec_ref(v_a_406_);
lean_dec(v_a_405_);
lean_dec_ref(v_a_404_);
lean_dec(v_inst_401_);
return v_res_409_;
}
}
static lean_object* _init_l_Lean_Meta_PProdN_pack___closed__5(void){
_start:
{
lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_417_ = lean_box(0);
v___x_418_ = ((lean_object*)(l_Lean_Meta_PProdN_pack___closed__4));
v___x_419_ = l_Lean_Expr_const___override(v___x_418_, v___x_417_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_pack(lean_object* v_lvl_420_, lean_object* v_xs_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; uint8_t v___x_429_; 
v___x_427_ = lean_array_get_size(v_xs_421_);
v___x_428_ = lean_unsigned_to_nat(0u);
v___x_429_ = lean_nat_dec_eq(v___x_427_, v___x_428_);
if (v___x_429_ == 0)
{
lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
lean_dec(v_lvl_420_);
v___x_430_ = l_Lean_instInhabitedExpr;
v___x_431_ = ((lean_object*)(l_Lean_Meta_PProdN_pack___closed__0));
v___x_432_ = l_Lean_Meta_PProdN_genMk___redArg(v___x_430_, v___x_431_, v_xs_421_, v_a_422_, v_a_423_, v_a_424_, v_a_425_);
return v___x_432_;
}
else
{
uint8_t v___x_433_; 
lean_dec_ref(v_xs_421_);
v___x_433_ = l_Lean_Level_isAlwaysZero(v_lvl_420_);
if (v___x_433_ == 0)
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_434_ = ((lean_object*)(l_Lean_Meta_PProdN_pack___closed__2));
v___x_435_ = lean_box(0);
v___x_436_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_436_, 0, v_lvl_420_);
lean_ctor_set(v___x_436_, 1, v___x_435_);
v___x_437_ = l_Lean_Expr_const___override(v___x_434_, v___x_436_);
v___x_438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_438_, 0, v___x_437_);
return v___x_438_;
}
else
{
lean_object* v___x_439_; lean_object* v___x_440_; 
lean_dec(v_lvl_420_);
v___x_439_ = lean_obj_once(&l_Lean_Meta_PProdN_pack___closed__5, &l_Lean_Meta_PProdN_pack___closed__5_once, _init_l_Lean_Meta_PProdN_pack___closed__5);
v___x_440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_440_, 0, v___x_439_);
return v___x_440_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_pack___boxed(lean_object* v_lvl_441_, lean_object* v_xs_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l_Lean_Meta_PProdN_pack(v_lvl_441_, v_xs_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_);
lean_dec(v_a_446_);
lean_dec_ref(v_a_445_);
lean_dec(v_a_444_);
lean_dec_ref(v_a_443_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_unpack_go___redArg(lean_object* v_e_449_, lean_object* v_remaining_450_, lean_object* v_acc_451_){
_start:
{
lean_object* v___x_456_; uint8_t v___x_457_; 
v___x_456_ = lean_unsigned_to_nat(0u);
v___x_457_ = lean_nat_dec_eq(v_remaining_450_, v___x_456_);
if (v___x_457_ == 0)
{
if (lean_obj_tag(v_e_449_) == 5)
{
lean_object* v_fn_458_; 
v_fn_458_ = lean_ctor_get(v_e_449_, 0);
if (lean_obj_tag(v_fn_458_) == 5)
{
lean_object* v_fn_459_; 
v_fn_459_ = lean_ctor_get(v_fn_458_, 0);
if (lean_obj_tag(v_fn_459_) == 4)
{
lean_object* v_declName_460_; 
v_declName_460_ = lean_ctor_get(v_fn_459_, 0);
if (lean_obj_tag(v_declName_460_) == 1)
{
lean_object* v_pre_461_; 
v_pre_461_ = lean_ctor_get(v_declName_460_, 0);
if (lean_obj_tag(v_pre_461_) == 0)
{
lean_object* v_arg_462_; lean_object* v_arg_463_; lean_object* v_str_464_; lean_object* v___x_465_; uint8_t v___x_466_; 
v_arg_462_ = lean_ctor_get(v_e_449_, 1);
v_arg_463_ = lean_ctor_get(v_fn_458_, 1);
v_str_464_ = lean_ctor_get(v_declName_460_, 1);
v___x_465_ = ((lean_object*)(l_Lean_Meta_mkPProd___closed__0));
v___x_466_ = lean_string_dec_eq(v_str_464_, v___x_465_);
if (v___x_466_ == 0)
{
lean_dec(v_remaining_450_);
goto v___jp_453_;
}
else
{
lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
lean_inc_ref(v_arg_463_);
lean_inc_ref(v_arg_462_);
lean_dec_ref_known(v_e_449_, 2);
v___x_467_ = lean_unsigned_to_nat(1u);
v___x_468_ = lean_nat_sub(v_remaining_450_, v___x_467_);
lean_dec(v_remaining_450_);
v___x_469_ = lean_array_push(v_acc_451_, v_arg_463_);
v_e_449_ = v_arg_462_;
v_remaining_450_ = v___x_468_;
v_acc_451_ = v___x_469_;
goto _start;
}
}
else
{
lean_dec(v_remaining_450_);
goto v___jp_453_;
}
}
else
{
lean_dec(v_remaining_450_);
goto v___jp_453_;
}
}
else
{
lean_dec(v_remaining_450_);
goto v___jp_453_;
}
}
else
{
lean_dec(v_remaining_450_);
goto v___jp_453_;
}
}
else
{
lean_dec(v_remaining_450_);
goto v___jp_453_;
}
}
else
{
lean_object* v___x_471_; 
lean_dec(v_remaining_450_);
lean_dec_ref(v_e_449_);
v___x_471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_471_, 0, v_acc_451_);
return v___x_471_;
}
v___jp_453_:
{
lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_454_ = lean_array_push(v_acc_451_, v_e_449_);
v___x_455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_455_, 0, v___x_454_);
return v___x_455_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_unpack_go___redArg___boxed(lean_object* v_e_472_, lean_object* v_remaining_473_, lean_object* v_acc_474_, lean_object* v_a_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_unpack_go___redArg(v_e_472_, v_remaining_473_, v_acc_474_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_unpack_go(lean_object* v_e_477_, lean_object* v_remaining_478_, lean_object* v_acc_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_){
_start:
{
lean_object* v___x_485_; 
v___x_485_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_unpack_go___redArg(v_e_477_, v_remaining_478_, v_acc_479_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_unpack_go___boxed(lean_object* v_e_486_, lean_object* v_remaining_487_, lean_object* v_acc_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_unpack_go(v_e_486_, v_remaining_487_, v_acc_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_);
lean_dec(v_a_492_);
lean_dec_ref(v_a_491_);
lean_dec(v_a_490_);
lean_dec_ref(v_a_489_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_unpack___redArg(lean_object* v_e_497_, lean_object* v_n_498_){
_start:
{
if (lean_obj_tag(v_e_497_) == 4)
{
lean_object* v_declName_506_; 
v_declName_506_ = lean_ctor_get(v_e_497_, 0);
if (lean_obj_tag(v_declName_506_) == 1)
{
lean_object* v_pre_507_; 
v_pre_507_ = lean_ctor_get(v_declName_506_, 0);
if (lean_obj_tag(v_pre_507_) == 0)
{
lean_object* v_str_508_; lean_object* v___x_509_; uint8_t v___x_510_; 
v_str_508_ = lean_ctor_get(v_declName_506_, 1);
v___x_509_ = ((lean_object*)(l_Lean_Meta_PProdN_pack___closed__3));
v___x_510_ = lean_string_dec_eq(v_str_508_, v___x_509_);
if (v___x_510_ == 0)
{
lean_object* v___x_511_; uint8_t v___x_512_; 
v___x_511_ = ((lean_object*)(l_Lean_Meta_PProdN_pack___closed__1));
v___x_512_ = lean_string_dec_eq(v_str_508_, v___x_511_);
if (v___x_512_ == 0)
{
goto v___jp_500_;
}
else
{
lean_dec_ref_known(v_e_497_, 2);
lean_dec(v_n_498_);
goto v___jp_503_;
}
}
else
{
lean_dec_ref_known(v_e_497_, 2);
lean_dec(v_n_498_);
goto v___jp_503_;
}
}
else
{
goto v___jp_500_;
}
}
else
{
goto v___jp_500_;
}
}
else
{
goto v___jp_500_;
}
v___jp_500_:
{
lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_501_ = ((lean_object*)(l_Lean_Meta_PProdN_unpack___redArg___closed__0));
v___x_502_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_unpack_go___redArg(v_e_497_, v_n_498_, v___x_501_);
return v___x_502_;
}
v___jp_503_:
{
lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_504_ = ((lean_object*)(l_Lean_Meta_PProdN_unpack___redArg___closed__0));
v___x_505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_505_, 0, v___x_504_);
return v___x_505_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_unpack___redArg___boxed(lean_object* v_e_513_, lean_object* v_n_514_, lean_object* v_a_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l_Lean_Meta_PProdN_unpack___redArg(v_e_513_, v_n_514_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_unpack(lean_object* v_e_517_, lean_object* v_n_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_){
_start:
{
lean_object* v___x_524_; 
v___x_524_ = l_Lean_Meta_PProdN_unpack___redArg(v_e_517_, v_n_518_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_unpack___boxed(lean_object* v_e_525_, lean_object* v_n_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_Lean_Meta_PProdN_unpack(v_e_525_, v_n_526_, v_a_527_, v_a_528_, v_a_529_, v_a_530_);
lean_dec(v_a_530_);
lean_dec_ref(v_a_529_);
lean_dec(v_a_528_);
lean_dec_ref(v_a_527_);
return v_res_532_;
}
}
static lean_object* _init_l_Lean_Meta_PProdN_mk___closed__4(void){
_start:
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_541_ = lean_box(0);
v___x_542_ = ((lean_object*)(l_Lean_Meta_PProdN_mk___closed__3));
v___x_543_ = l_Lean_Expr_const___override(v___x_542_, v___x_541_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_mk(lean_object* v_lvl_544_, lean_object* v_xs_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_){
_start:
{
lean_object* v___x_551_; lean_object* v___x_552_; uint8_t v___x_553_; 
v___x_551_ = lean_array_get_size(v_xs_545_);
v___x_552_ = lean_unsigned_to_nat(0u);
v___x_553_ = lean_nat_dec_eq(v___x_551_, v___x_552_);
if (v___x_553_ == 0)
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
lean_dec(v_lvl_544_);
v___x_554_ = l_Lean_instInhabitedExpr;
v___x_555_ = ((lean_object*)(l_Lean_Meta_PProdN_mk___closed__0));
v___x_556_ = l_Lean_Meta_PProdN_genMk___redArg(v___x_554_, v___x_555_, v_xs_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_);
return v___x_556_;
}
else
{
uint8_t v___x_557_; 
lean_dec_ref(v_xs_545_);
v___x_557_ = l_Lean_Level_isAlwaysZero(v_lvl_544_);
if (v___x_557_ == 0)
{
lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_558_ = ((lean_object*)(l_Lean_Meta_PProdN_mk___closed__2));
v___x_559_ = lean_box(0);
v___x_560_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_560_, 0, v_lvl_544_);
lean_ctor_set(v___x_560_, 1, v___x_559_);
v___x_561_ = l_Lean_Expr_const___override(v___x_558_, v___x_560_);
v___x_562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_562_, 0, v___x_561_);
return v___x_562_;
}
else
{
lean_object* v___x_563_; lean_object* v___x_564_; 
lean_dec(v_lvl_544_);
v___x_563_ = lean_obj_once(&l_Lean_Meta_PProdN_mk___closed__4, &l_Lean_Meta_PProdN_mk___closed__4_once, _init_l_Lean_Meta_PProdN_mk___closed__4);
v___x_564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_564_, 0, v___x_563_);
return v___x_564_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_mk___boxed(lean_object* v_lvl_565_, lean_object* v_xs_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_Lean_Meta_PProdN_mk(v_lvl_565_, v_xs_566_, v_a_567_, v_a_568_, v_a_569_, v_a_570_);
lean_dec(v_a_570_);
lean_dec_ref(v_a_569_);
lean_dec(v_a_568_);
lean_dec_ref(v_a_567_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_proj_spec__0___redArg(lean_object* v_upperBound_573_, lean_object* v_a_574_, lean_object* v_b_575_){
_start:
{
uint8_t v___x_576_; 
v___x_576_ = lean_nat_dec_lt(v_a_574_, v_upperBound_573_);
if (v___x_576_ == 0)
{
lean_dec(v_a_574_);
return v_b_575_;
}
else
{
lean_object* v_fst_577_; lean_object* v_snd_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_590_; 
v_fst_577_ = lean_ctor_get(v_b_575_, 0);
v_snd_578_ = lean_ctor_get(v_b_575_, 1);
v_isSharedCheck_590_ = !lean_is_exclusive(v_b_575_);
if (v_isSharedCheck_590_ == 0)
{
v___x_580_ = v_b_575_;
v_isShared_581_ = v_isSharedCheck_590_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_snd_578_);
lean_inc(v_fst_577_);
lean_dec(v_b_575_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_590_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_585_; 
v___x_582_ = l_Lean_Meta_mkPProdSnd(v_fst_577_, v_snd_578_);
v___x_583_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_mkTypeSnd(v_fst_577_);
lean_dec(v_fst_577_);
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 1, v___x_582_);
lean_ctor_set(v___x_580_, 0, v___x_583_);
v___x_585_ = v___x_580_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v___x_583_);
lean_ctor_set(v_reuseFailAlloc_589_, 1, v___x_582_);
v___x_585_ = v_reuseFailAlloc_589_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_586_ = lean_unsigned_to_nat(1u);
v___x_587_ = lean_nat_add(v_a_574_, v___x_586_);
lean_dec(v_a_574_);
v_a_574_ = v___x_587_;
v_b_575_ = v___x_585_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_proj_spec__0___redArg___boxed(lean_object* v_upperBound_591_, lean_object* v_a_592_, lean_object* v_b_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_proj_spec__0___redArg(v_upperBound_591_, v_a_592_, v_b_593_);
lean_dec(v_upperBound_591_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_proj(lean_object* v_n_595_, lean_object* v_i_596_, lean_object* v_t_597_, lean_object* v_e_598_){
_start:
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v_fst_602_; lean_object* v_snd_603_; lean_object* v___x_604_; lean_object* v___x_605_; uint8_t v___x_606_; 
v___x_599_ = lean_unsigned_to_nat(0u);
v___x_600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_600_, 0, v_t_597_);
lean_ctor_set(v___x_600_, 1, v_e_598_);
v___x_601_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_proj_spec__0___redArg(v_i_596_, v___x_599_, v___x_600_);
v_fst_602_ = lean_ctor_get(v___x_601_, 0);
lean_inc(v_fst_602_);
v_snd_603_ = lean_ctor_get(v___x_601_, 1);
lean_inc(v_snd_603_);
lean_dec_ref(v___x_601_);
v___x_604_ = lean_unsigned_to_nat(1u);
v___x_605_ = lean_nat_add(v_i_596_, v___x_604_);
v___x_606_ = lean_nat_dec_lt(v___x_605_, v_n_595_);
lean_dec(v___x_605_);
if (v___x_606_ == 0)
{
lean_dec(v_fst_602_);
return v_snd_603_;
}
else
{
lean_object* v___x_607_; 
v___x_607_ = l_Lean_Meta_mkPProdFst(v_fst_602_, v_snd_603_);
lean_dec(v_fst_602_);
return v___x_607_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_proj___boxed(lean_object* v_n_608_, lean_object* v_i_609_, lean_object* v_t_610_, lean_object* v_e_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = l_Lean_Meta_PProdN_proj(v_n_608_, v_i_609_, v_t_610_, v_e_611_);
lean_dec(v_i_609_);
lean_dec(v_n_608_);
return v_res_612_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_proj_spec__0(lean_object* v_upperBound_613_, lean_object* v_inst_614_, lean_object* v_R_615_, lean_object* v_a_616_, lean_object* v_b_617_, lean_object* v_c_618_){
_start:
{
lean_object* v___x_619_; 
v___x_619_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_proj_spec__0___redArg(v_upperBound_613_, v_a_616_, v_b_617_);
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_proj_spec__0___boxed(lean_object* v_upperBound_620_, lean_object* v_inst_621_, lean_object* v_R_622_, lean_object* v_a_623_, lean_object* v_b_624_, lean_object* v_c_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_proj_spec__0(v_upperBound_620_, v_inst_621_, v_R_622_, v_a_623_, v_b_624_, v_c_625_);
lean_dec(v_upperBound_620_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_projs___lam__0(lean_object* v_n_627_, lean_object* v_t_628_, lean_object* v_e_629_, lean_object* v_i_630_){
_start:
{
lean_object* v___x_631_; 
v___x_631_ = l_Lean_Meta_PProdN_proj(v_n_627_, v_i_630_, v_t_628_, v_e_629_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_projs___lam__0___boxed(lean_object* v_n_632_, lean_object* v_t_633_, lean_object* v_e_634_, lean_object* v_i_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l_Lean_Meta_PProdN_projs___lam__0(v_n_632_, v_t_633_, v_e_634_, v_i_635_);
lean_dec(v_i_635_);
lean_dec(v_n_632_);
return v_res_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_projs(lean_object* v_n_637_, lean_object* v_t_638_, lean_object* v_e_639_){
_start:
{
lean_object* v___f_640_; lean_object* v___x_641_; 
lean_inc(v_n_637_);
v___f_640_ = lean_alloc_closure((void*)(l_Lean_Meta_PProdN_projs___lam__0___boxed), 4, 3);
lean_closure_set(v___f_640_, 0, v_n_637_);
lean_closure_set(v___f_640_, 1, v_t_638_);
lean_closure_set(v___f_640_, 2, v_e_639_);
v___x_641_ = l_Array_ofFn___redArg(v_n_637_, v___f_640_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_projM_spec__0___redArg(lean_object* v_upperBound_642_, lean_object* v_a_643_, lean_object* v_b_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_){
_start:
{
uint8_t v___x_650_; 
v___x_650_ = lean_nat_dec_lt(v_a_643_, v_upperBound_642_);
if (v___x_650_ == 0)
{
lean_object* v___x_651_; 
lean_dec(v_a_643_);
v___x_651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_651_, 0, v_b_644_);
return v___x_651_;
}
else
{
lean_object* v___x_652_; 
v___x_652_ = l_Lean_Meta_mkPProdSndM(v_b_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_);
if (lean_obj_tag(v___x_652_) == 0)
{
lean_object* v_a_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v_a_653_ = lean_ctor_get(v___x_652_, 0);
lean_inc(v_a_653_);
lean_dec_ref_known(v___x_652_, 1);
v___x_654_ = lean_unsigned_to_nat(1u);
v___x_655_ = lean_nat_add(v_a_643_, v___x_654_);
lean_dec(v_a_643_);
v_a_643_ = v___x_655_;
v_b_644_ = v_a_653_;
goto _start;
}
else
{
lean_dec(v_a_643_);
return v___x_652_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_projM_spec__0___redArg___boxed(lean_object* v_upperBound_657_, lean_object* v_a_658_, lean_object* v_b_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_projM_spec__0___redArg(v_upperBound_657_, v_a_658_, v_b_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec(v_upperBound_657_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_projM(lean_object* v_n_666_, lean_object* v_i_667_, lean_object* v_e_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_){
_start:
{
lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_674_ = lean_unsigned_to_nat(0u);
v___x_675_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_projM_spec__0___redArg(v_i_667_, v___x_674_, v_e_668_, v_a_669_, v_a_670_, v_a_671_, v_a_672_);
if (lean_obj_tag(v___x_675_) == 0)
{
lean_object* v_a_676_; lean_object* v___x_677_; lean_object* v___x_678_; uint8_t v___x_679_; 
v_a_676_ = lean_ctor_get(v___x_675_, 0);
v___x_677_ = lean_unsigned_to_nat(1u);
v___x_678_ = lean_nat_add(v_i_667_, v___x_677_);
v___x_679_ = lean_nat_dec_lt(v___x_678_, v_n_666_);
lean_dec(v___x_678_);
if (v___x_679_ == 0)
{
return v___x_675_;
}
else
{
lean_object* v___x_680_; 
lean_inc(v_a_676_);
lean_dec_ref_known(v___x_675_, 1);
v___x_680_ = l_Lean_Meta_mkPProdFstM(v_a_676_, v_a_669_, v_a_670_, v_a_671_, v_a_672_);
return v___x_680_;
}
}
else
{
return v___x_675_;
}
}
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_projM_spec__0(lean_object* v_upperBound_690_, lean_object* v_inst_691_, lean_object* v_R_692_, lean_object* v_a_693_, lean_object* v_b_694_, lean_object* v_c_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_){
_start:
{
lean_object* v___x_701_; 
v___x_701_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_projM_spec__0___redArg(v_upperBound_690_, v_a_693_, v_b_694_, v___y_696_, v___y_697_, v___y_698_, v___y_699_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_projM_spec__0___boxed(lean_object* v_upperBound_702_, lean_object* v_inst_703_, lean_object* v_R_704_, lean_object* v_a_705_, lean_object* v_b_706_, lean_object* v_c_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_projM_spec__0(v_upperBound_702_, v_inst_703_, v_R_704_, v_a_705_, v_b_706_, v_c_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_);
lean_dec(v___y_711_);
lean_dec_ref(v___y_710_);
lean_dec(v___y_709_);
lean_dec_ref(v___y_708_);
lean_dec(v_upperBound_702_);
return v_res_713_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_PProdN_packLambdas_spec__0(lean_object* v_msg_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
lean_object* v___f_720_; lean_object* v___x_336__overap_721_; lean_object* v___x_722_; 
v___f_720_ = ((lean_object*)(l_Lean_Meta_PProdN_genMk___redArg___closed__6));
v___x_336__overap_721_ = lean_panic_fn_borrowed(v___f_720_, v_msg_714_);
lean_inc(v___y_718_);
lean_inc_ref(v___y_717_);
lean_inc(v___y_716_);
lean_inc_ref(v___y_715_);
v___x_722_ = lean_apply_5(v___x_336__overap_721_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, lean_box(0));
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_PProdN_packLambdas_spec__0___boxed(lean_object* v_msg_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l_panic___at___00Lean_Meta_PProdN_packLambdas_spec__0(v_msg_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_);
lean_dec(v___y_727_);
lean_dec_ref(v___y_726_);
lean_dec(v___y_725_);
lean_dec_ref(v___y_724_);
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___redArg___lam__0(lean_object* v_k_730_, lean_object* v_b_731_, lean_object* v_c_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_){
_start:
{
lean_object* v___x_738_; 
lean_inc(v___y_736_);
lean_inc_ref(v___y_735_);
lean_inc(v___y_734_);
lean_inc_ref(v___y_733_);
v___x_738_ = lean_apply_7(v_k_730_, v_b_731_, v_c_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, lean_box(0));
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___redArg___lam__0___boxed(lean_object* v_k_739_, lean_object* v_b_740_, lean_object* v_c_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___redArg___lam__0(v_k_739_, v_b_740_, v_c_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_);
lean_dec(v___y_745_);
lean_dec_ref(v___y_744_);
lean_dec(v___y_743_);
lean_dec_ref(v___y_742_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___redArg(lean_object* v_type_748_, lean_object* v_k_749_, uint8_t v_cleanupAnnotations_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_){
_start:
{
lean_object* v___f_756_; uint8_t v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; 
v___f_756_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_756_, 0, v_k_749_);
v___x_757_ = 0;
v___x_758_ = lean_box(0);
v___x_759_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_757_, v___x_758_, v_type_748_, v___f_756_, v_cleanupAnnotations_750_, v___x_757_, v___y_751_, v___y_752_, v___y_753_, v___y_754_);
if (lean_obj_tag(v___x_759_) == 0)
{
lean_object* v_a_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_767_; 
v_a_760_ = lean_ctor_get(v___x_759_, 0);
v_isSharedCheck_767_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_767_ == 0)
{
v___x_762_ = v___x_759_;
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_a_760_);
lean_dec(v___x_759_);
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
v_reuseFailAlloc_766_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_775_; 
v_a_768_ = lean_ctor_get(v___x_759_, 0);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_775_ == 0)
{
v___x_770_ = v___x_759_;
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_a_768_);
lean_dec(v___x_759_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_773_; 
if (v_isShared_771_ == 0)
{
v___x_773_ = v___x_770_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_a_768_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___redArg___boxed(lean_object* v_type_776_, lean_object* v_k_777_, lean_object* v_cleanupAnnotations_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_784_; lean_object* v_res_785_; 
v_cleanupAnnotations_boxed_784_ = lean_unbox(v_cleanupAnnotations_778_);
v_res_785_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___redArg(v_type_776_, v_k_777_, v_cleanupAnnotations_boxed_784_, v___y_779_, v___y_780_, v___y_781_, v___y_782_);
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2(lean_object* v_00_u03b1_786_, lean_object* v_type_787_, lean_object* v_k_788_, uint8_t v_cleanupAnnotations_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_){
_start:
{
lean_object* v___x_795_; 
v___x_795_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___redArg(v_type_787_, v_k_788_, v_cleanupAnnotations_789_, v___y_790_, v___y_791_, v___y_792_, v___y_793_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___boxed(lean_object* v_00_u03b1_796_, lean_object* v_type_797_, lean_object* v_k_798_, lean_object* v_cleanupAnnotations_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_805_; lean_object* v_res_806_; 
v_cleanupAnnotations_boxed_805_ = lean_unbox(v_cleanupAnnotations_799_);
v_res_806_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2(v_00_u03b1_796_, v_type_797_, v_k_798_, v_cleanupAnnotations_boxed_805_, v___y_800_, v___y_801_, v___y_802_, v___y_803_);
lean_dec(v___y_803_);
lean_dec_ref(v___y_802_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_PProdN_packLambdas_spec__1(lean_object* v_xs_807_, size_t v_sz_808_, size_t v_i_809_, lean_object* v_bs_810_){
_start:
{
uint8_t v___x_811_; 
v___x_811_ = lean_usize_dec_lt(v_i_809_, v_sz_808_);
if (v___x_811_ == 0)
{
lean_dec_ref(v_xs_807_);
return v_bs_810_;
}
else
{
lean_object* v_v_812_; lean_object* v___x_813_; lean_object* v_bs_x27_814_; lean_object* v___x_815_; size_t v___x_816_; size_t v___x_817_; lean_object* v___x_818_; 
v_v_812_ = lean_array_uget(v_bs_810_, v_i_809_);
v___x_813_ = lean_unsigned_to_nat(0u);
v_bs_x27_814_ = lean_array_uset(v_bs_810_, v_i_809_, v___x_813_);
lean_inc_ref(v_xs_807_);
v___x_815_ = l_Lean_Expr_beta(v_v_812_, v_xs_807_);
v___x_816_ = ((size_t)1ULL);
v___x_817_ = lean_usize_add(v_i_809_, v___x_816_);
v___x_818_ = lean_array_uset(v_bs_x27_814_, v_i_809_, v___x_815_);
v_i_809_ = v___x_817_;
v_bs_810_ = v___x_818_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_PProdN_packLambdas_spec__1___boxed(lean_object* v_xs_820_, lean_object* v_sz_821_, lean_object* v_i_822_, lean_object* v_bs_823_){
_start:
{
size_t v_sz_boxed_824_; size_t v_i_boxed_825_; lean_object* v_res_826_; 
v_sz_boxed_824_ = lean_unbox_usize(v_sz_821_);
lean_dec(v_sz_821_);
v_i_boxed_825_ = lean_unbox_usize(v_i_822_);
lean_dec(v_i_822_);
v_res_826_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_PProdN_packLambdas_spec__1(v_xs_820_, v_sz_boxed_824_, v_i_boxed_825_, v_bs_823_);
return v_res_826_;
}
}
static lean_object* _init_l_Lean_Meta_PProdN_packLambdas___lam__0___closed__2(void){
_start:
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; 
v___x_829_ = ((lean_object*)(l_Lean_Meta_PProdN_packLambdas___lam__0___closed__1));
v___x_830_ = lean_unsigned_to_nat(4u);
v___x_831_ = lean_unsigned_to_nat(175u);
v___x_832_ = ((lean_object*)(l_Lean_Meta_PProdN_packLambdas___lam__0___closed__0));
v___x_833_ = ((lean_object*)(l_Lean_Meta_mkPProdFst___closed__0));
v___x_834_ = l_mkPanicMessageWithDecl(v___x_833_, v___x_832_, v___x_831_, v___x_830_, v___x_829_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_packLambdas___lam__0(lean_object* v_es_835_, uint8_t v___x_836_, lean_object* v_xs_837_, lean_object* v_sort_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_){
_start:
{
uint8_t v___x_844_; 
v___x_844_ = l_Lean_Expr_isSort(v_sort_838_);
if (v___x_844_ == 0)
{
lean_object* v___x_845_; lean_object* v___x_846_; 
lean_dec_ref(v_xs_837_);
lean_dec_ref(v_es_835_);
v___x_845_ = lean_obj_once(&l_Lean_Meta_PProdN_packLambdas___lam__0___closed__2, &l_Lean_Meta_PProdN_packLambdas___lam__0___closed__2_once, _init_l_Lean_Meta_PProdN_packLambdas___lam__0___closed__2);
v___x_846_ = l_panic___at___00Lean_Meta_PProdN_packLambdas_spec__0(v___x_845_, v___y_839_, v___y_840_, v___y_841_, v___y_842_);
return v___x_846_;
}
else
{
size_t v_sz_847_; size_t v___x_848_; lean_object* v_es_x27_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
v_sz_847_ = lean_array_size(v_es_835_);
v___x_848_ = ((size_t)0ULL);
lean_inc_ref(v_xs_837_);
v_es_x27_849_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_PProdN_packLambdas_spec__1(v_xs_837_, v_sz_847_, v___x_848_, v_es_835_);
v___x_850_ = l_Lean_Expr_sortLevel_x21(v_sort_838_);
v___x_851_ = l_Lean_Meta_PProdN_pack(v___x_850_, v_es_x27_849_, v___y_839_, v___y_840_, v___y_841_, v___y_842_);
if (lean_obj_tag(v___x_851_) == 0)
{
lean_object* v_a_852_; uint8_t v___x_853_; lean_object* v___x_854_; 
v_a_852_ = lean_ctor_get(v___x_851_, 0);
lean_inc(v_a_852_);
lean_dec_ref_known(v___x_851_, 1);
v___x_853_ = 1;
v___x_854_ = l_Lean_Meta_mkLambdaFVars(v_xs_837_, v_a_852_, v___x_836_, v___x_844_, v___x_836_, v___x_844_, v___x_853_, v___y_839_, v___y_840_, v___y_841_, v___y_842_);
lean_dec_ref(v_xs_837_);
return v___x_854_;
}
else
{
lean_dec_ref(v_xs_837_);
return v___x_851_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_packLambdas___lam__0___boxed(lean_object* v_es_855_, lean_object* v___x_856_, lean_object* v_xs_857_, lean_object* v_sort_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_){
_start:
{
uint8_t v___x_936__boxed_864_; lean_object* v_res_865_; 
v___x_936__boxed_864_ = lean_unbox(v___x_856_);
v_res_865_ = l_Lean_Meta_PProdN_packLambdas___lam__0(v_es_855_, v___x_936__boxed_864_, v_xs_857_, v_sort_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_);
lean_dec(v___y_862_);
lean_dec_ref(v___y_861_);
lean_dec(v___y_860_);
lean_dec_ref(v___y_859_);
lean_dec_ref(v_sort_858_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_packLambdas(lean_object* v_type_866_, lean_object* v_es_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_){
_start:
{
lean_object* v___x_873_; lean_object* v___x_874_; uint8_t v___x_875_; 
v___x_873_ = lean_array_get_size(v_es_867_);
v___x_874_ = lean_unsigned_to_nat(1u);
v___x_875_ = lean_nat_dec_eq(v___x_873_, v___x_874_);
if (v___x_875_ == 0)
{
lean_object* v___x_876_; lean_object* v___f_877_; lean_object* v___x_878_; 
v___x_876_ = lean_box(v___x_875_);
v___f_877_ = lean_alloc_closure((void*)(l_Lean_Meta_PProdN_packLambdas___lam__0___boxed), 9, 2);
lean_closure_set(v___f_877_, 0, v_es_867_);
lean_closure_set(v___f_877_, 1, v___x_876_);
v___x_878_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___redArg(v_type_866_, v___f_877_, v___x_875_, v_a_868_, v_a_869_, v_a_870_, v_a_871_);
return v___x_878_;
}
else
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
lean_dec_ref(v_type_866_);
v___x_879_ = lean_unsigned_to_nat(0u);
v___x_880_ = lean_array_fget(v_es_867_, v___x_879_);
lean_dec_ref(v_es_867_);
v___x_881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_881_, 0, v___x_880_);
return v___x_881_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_packLambdas___boxed(lean_object* v_type_882_, lean_object* v_es_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l_Lean_Meta_PProdN_packLambdas(v_type_882_, v_es_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_);
lean_dec(v_a_887_);
lean_dec_ref(v_a_886_);
lean_dec(v_a_885_);
lean_dec_ref(v_a_884_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_mkLambdas___lam__0(lean_object* v_es_890_, uint8_t v___x_891_, lean_object* v_xs_892_, lean_object* v_body_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_){
_start:
{
lean_object* v___x_899_; 
v___x_899_ = l_Lean_Meta_getLevel(v_body_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_);
if (lean_obj_tag(v___x_899_) == 0)
{
lean_object* v_a_900_; size_t v_sz_901_; size_t v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; 
v_a_900_ = lean_ctor_get(v___x_899_, 0);
lean_inc(v_a_900_);
lean_dec_ref_known(v___x_899_, 1);
v_sz_901_ = lean_array_size(v_es_890_);
v___x_902_ = ((size_t)0ULL);
lean_inc_ref(v_xs_892_);
v___x_903_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_PProdN_packLambdas_spec__1(v_xs_892_, v_sz_901_, v___x_902_, v_es_890_);
v___x_904_ = l_Lean_Meta_PProdN_mk(v_a_900_, v___x_903_, v___y_894_, v___y_895_, v___y_896_, v___y_897_);
if (lean_obj_tag(v___x_904_) == 0)
{
lean_object* v_a_905_; uint8_t v___x_906_; uint8_t v___x_907_; lean_object* v___x_908_; 
v_a_905_ = lean_ctor_get(v___x_904_, 0);
lean_inc(v_a_905_);
lean_dec_ref_known(v___x_904_, 1);
v___x_906_ = 1;
v___x_907_ = 1;
v___x_908_ = l_Lean_Meta_mkLambdaFVars(v_xs_892_, v_a_905_, v___x_891_, v___x_906_, v___x_891_, v___x_906_, v___x_907_, v___y_894_, v___y_895_, v___y_896_, v___y_897_);
lean_dec_ref(v_xs_892_);
return v___x_908_;
}
else
{
lean_dec_ref(v_xs_892_);
return v___x_904_;
}
}
else
{
lean_object* v_a_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_916_; 
lean_dec_ref(v_xs_892_);
lean_dec_ref(v_es_890_);
v_a_909_ = lean_ctor_get(v___x_899_, 0);
v_isSharedCheck_916_ = !lean_is_exclusive(v___x_899_);
if (v_isSharedCheck_916_ == 0)
{
v___x_911_ = v___x_899_;
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_a_909_);
lean_dec(v___x_899_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v___x_914_; 
if (v_isShared_912_ == 0)
{
v___x_914_ = v___x_911_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v_a_909_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_mkLambdas___lam__0___boxed(lean_object* v_es_917_, lean_object* v___x_918_, lean_object* v_xs_919_, lean_object* v_body_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_){
_start:
{
uint8_t v___x_364__boxed_926_; lean_object* v_res_927_; 
v___x_364__boxed_926_ = lean_unbox(v___x_918_);
v_res_927_ = l_Lean_Meta_PProdN_mkLambdas___lam__0(v_es_917_, v___x_364__boxed_926_, v_xs_919_, v_body_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
lean_dec(v___y_924_);
lean_dec_ref(v___y_923_);
lean_dec(v___y_922_);
lean_dec_ref(v___y_921_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_mkLambdas(lean_object* v_type_928_, lean_object* v_es_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_){
_start:
{
lean_object* v___x_935_; lean_object* v___x_936_; uint8_t v___x_937_; 
v___x_935_ = lean_array_get_size(v_es_929_);
v___x_936_ = lean_unsigned_to_nat(1u);
v___x_937_ = lean_nat_dec_eq(v___x_935_, v___x_936_);
if (v___x_937_ == 0)
{
lean_object* v___x_938_; lean_object* v___f_939_; lean_object* v___x_940_; 
v___x_938_ = lean_box(v___x_937_);
v___f_939_ = lean_alloc_closure((void*)(l_Lean_Meta_PProdN_mkLambdas___lam__0___boxed), 9, 2);
lean_closure_set(v___f_939_, 0, v_es_929_);
lean_closure_set(v___f_939_, 1, v___x_938_);
v___x_940_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___redArg(v_type_928_, v___f_939_, v___x_937_, v_a_930_, v_a_931_, v_a_932_, v_a_933_);
return v___x_940_;
}
else
{
lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
lean_dec_ref(v_type_928_);
v___x_941_ = lean_unsigned_to_nat(0u);
v___x_942_ = lean_array_fget(v_es_929_, v___x_941_);
lean_dec_ref(v_es_929_);
v___x_943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_943_, 0, v___x_942_);
return v___x_943_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_mkLambdas___boxed(lean_object* v_type_944_, lean_object* v_es_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_Lean_Meta_PProdN_mkLambdas(v_type_944_, v_es_945_, v_a_946_, v_a_947_, v_a_948_, v_a_949_);
lean_dec(v_a_949_);
lean_dec_ref(v_a_948_);
lean_dec(v_a_947_);
lean_dec_ref(v_a_946_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_stripProjs(lean_object* v_e_952_){
_start:
{
if (lean_obj_tag(v_e_952_) == 11)
{
lean_object* v_typeName_953_; 
v_typeName_953_ = lean_ctor_get(v_e_952_, 0);
if (lean_obj_tag(v_typeName_953_) == 1)
{
lean_object* v_pre_954_; 
v_pre_954_ = lean_ctor_get(v_typeName_953_, 0);
if (lean_obj_tag(v_pre_954_) == 0)
{
lean_object* v_struct_955_; lean_object* v_str_956_; lean_object* v___x_957_; uint8_t v___x_958_; 
v_struct_955_ = lean_ctor_get(v_e_952_, 2);
v_str_956_ = lean_ctor_get(v_typeName_953_, 1);
v___x_957_ = ((lean_object*)(l_Lean_Meta_mkPProd___closed__0));
v___x_958_ = lean_string_dec_eq(v_str_956_, v___x_957_);
if (v___x_958_ == 0)
{
lean_object* v___x_959_; uint8_t v___x_960_; 
v___x_959_ = ((lean_object*)(l_Lean_Meta_mkPProd___closed__2));
v___x_960_ = lean_string_dec_eq(v_str_956_, v___x_959_);
if (v___x_960_ == 0)
{
lean_inc_ref(v_e_952_);
return v_e_952_;
}
else
{
v_e_952_ = v_struct_955_;
goto _start;
}
}
else
{
v_e_952_ = v_struct_955_;
goto _start;
}
}
else
{
lean_inc_ref(v_e_952_);
return v_e_952_;
}
}
else
{
lean_inc_ref(v_e_952_);
return v_e_952_;
}
}
else
{
lean_inc_ref(v_e_952_);
return v_e_952_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_stripProjs___boxed(lean_object* v_e_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_Lean_Meta_PProdN_stripProjs(v_e_963_);
lean_dec_ref(v_e_963_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___redArg(lean_object* v_e_967_, lean_object* v_i_968_){
_start:
{
lean_object* v___x_982_; lean_object* v___x_983_; uint8_t v___x_984_; 
v___x_982_ = ((lean_object*)(l_Lean_Meta_mkPProdMk___closed__1));
v___x_983_ = lean_unsigned_to_nat(4u);
v___x_984_ = l_Lean_Expr_isAppOfArity(v_e_967_, v___x_982_, v___x_983_);
if (v___x_984_ == 0)
{
lean_object* v___x_985_; lean_object* v___x_986_; uint8_t v___x_987_; 
v___x_985_ = ((lean_object*)(l_Lean_Meta_mkPProdMk___closed__3));
v___x_986_ = lean_unsigned_to_nat(2u);
v___x_987_ = l_Lean_Expr_isAppOfArity(v_e_967_, v___x_985_, v___x_986_);
if (v___x_987_ == 0)
{
lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_988_ = ((lean_object*)(l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___redArg___closed__0));
v___x_989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_989_, 0, v___x_988_);
return v___x_989_;
}
else
{
goto v___jp_970_;
}
}
else
{
goto v___jp_970_;
}
v___jp_970_:
{
lean_object* v___x_971_; uint8_t v___x_972_; 
v___x_971_ = lean_unsigned_to_nat(0u);
v___x_972_ = lean_nat_dec_eq(v_i_968_, v___x_971_);
if (v___x_972_ == 0)
{
lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_973_ = l_Lean_Expr_appArg_x21(v_e_967_);
v___x_974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_974_, 0, v___x_973_);
v___x_975_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_975_, 0, v___x_974_);
v___x_976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_976_, 0, v___x_975_);
return v___x_976_;
}
else
{
lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_977_ = l_Lean_Expr_appFn_x21(v_e_967_);
v___x_978_ = l_Lean_Expr_appArg_x21(v___x_977_);
lean_dec_ref(v___x_977_);
v___x_979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_979_, 0, v___x_978_);
v___x_980_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_980_, 0, v___x_979_);
v___x_981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_981_, 0, v___x_980_);
return v___x_981_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___redArg___boxed(lean_object* v_e_990_, lean_object* v_i_991_, lean_object* v_a_992_){
_start:
{
lean_object* v_res_993_; 
v_res_993_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___redArg(v_e_990_, v_i_991_);
lean_dec(v_i_991_);
lean_dec_ref(v_e_990_);
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce(lean_object* v_e_994_, lean_object* v_i_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_){
_start:
{
lean_object* v___x_1001_; 
v___x_1001_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___redArg(v_e_994_, v_i_995_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___boxed(lean_object* v_e_1002_, lean_object* v_i_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_){
_start:
{
lean_object* v_res_1009_; 
v_res_1009_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce(v_e_1002_, v_i_1003_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_);
lean_dec(v_a_1007_);
lean_dec_ref(v_a_1006_);
lean_dec(v_a_1005_);
lean_dec_ref(v_a_1004_);
lean_dec(v_i_1003_);
lean_dec_ref(v_e_1002_);
return v_res_1009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_reduceProjs___lam__0(lean_object* v_x_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_){
_start:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1016_ = ((lean_object*)(l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___redArg___closed__0));
v___x_1017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1016_);
return v___x_1017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_reduceProjs___lam__0___boxed(lean_object* v_x_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_){
_start:
{
lean_object* v_res_1024_; 
v_res_1024_ = l_Lean_Meta_PProdN_reduceProjs___lam__0(v_x_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_);
lean_dec(v___y_1022_);
lean_dec_ref(v___y_1021_);
lean_dec(v___y_1020_);
lean_dec_ref(v___y_1019_);
lean_dec_ref(v_x_1018_);
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_reduceProjs___lam__1(lean_object* v_e_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_){
_start:
{
lean_object* v_e_x27_1048_; lean_object* v_e_x27_1052_; lean_object* v___x_1062_; 
lean_inc_ref(v_e_1041_);
v___x_1062_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1041_, v___y_1043_);
if (lean_obj_tag(v___x_1062_) == 0)
{
lean_object* v_a_1063_; lean_object* v___x_1064_; uint8_t v___x_1065_; 
v_a_1063_ = lean_ctor_get(v___x_1062_, 0);
lean_inc(v_a_1063_);
lean_dec_ref_known(v___x_1062_, 1);
v___x_1064_ = l_Lean_Expr_cleanupAnnotations(v_a_1063_);
lean_dec(v_a_1063_);
v___x_1065_ = l_Lean_Expr_isApp(v___x_1064_);
if (v___x_1065_ == 0)
{
lean_dec_ref(v___x_1064_);
goto v___jp_1055_;
}
else
{
lean_object* v___x_1066_; uint8_t v___x_1067_; 
v___x_1066_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1064_);
v___x_1067_ = l_Lean_Expr_isApp(v___x_1066_);
if (v___x_1067_ == 0)
{
lean_dec_ref(v___x_1066_);
lean_dec_ref(v___x_1064_);
goto v___jp_1055_;
}
else
{
lean_object* v___x_1068_; uint8_t v___x_1069_; 
v___x_1068_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1066_);
lean_dec_ref(v___x_1066_);
v___x_1069_ = l_Lean_Expr_isApp(v___x_1068_);
if (v___x_1069_ == 0)
{
lean_dec_ref(v___x_1068_);
lean_dec_ref(v___x_1064_);
goto v___jp_1055_;
}
else
{
lean_object* v_arg_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; uint8_t v___x_1073_; 
v_arg_1070_ = lean_ctor_get(v___x_1064_, 1);
lean_inc_ref(v_arg_1070_);
lean_dec_ref(v___x_1064_);
v___x_1071_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1068_);
lean_dec_ref(v___x_1068_);
v___x_1072_ = ((lean_object*)(l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__1));
v___x_1073_ = l_Lean_Expr_isConstOf(v___x_1071_, v___x_1072_);
if (v___x_1073_ == 0)
{
lean_object* v___x_1074_; uint8_t v___x_1075_; 
v___x_1074_ = ((lean_object*)(l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__3));
v___x_1075_ = l_Lean_Expr_isConstOf(v___x_1071_, v___x_1074_);
if (v___x_1075_ == 0)
{
lean_object* v___x_1076_; uint8_t v___x_1077_; 
v___x_1076_ = ((lean_object*)(l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__5));
v___x_1077_ = l_Lean_Expr_isConstOf(v___x_1071_, v___x_1076_);
if (v___x_1077_ == 0)
{
lean_object* v___x_1078_; uint8_t v___x_1079_; 
v___x_1078_ = ((lean_object*)(l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__7));
v___x_1079_ = l_Lean_Expr_isConstOf(v___x_1071_, v___x_1078_);
lean_dec_ref(v___x_1071_);
if (v___x_1079_ == 0)
{
lean_dec_ref(v_arg_1070_);
goto v___jp_1055_;
}
else
{
lean_dec_ref(v_e_1041_);
v_e_x27_1052_ = v_arg_1070_;
goto v___jp_1051_;
}
}
else
{
lean_dec_ref(v___x_1071_);
lean_dec_ref(v_e_1041_);
v_e_x27_1052_ = v_arg_1070_;
goto v___jp_1051_;
}
}
else
{
lean_dec_ref(v___x_1071_);
lean_dec_ref(v_e_1041_);
v_e_x27_1048_ = v_arg_1070_;
goto v___jp_1047_;
}
}
else
{
lean_dec_ref(v___x_1071_);
lean_dec_ref(v_e_1041_);
v_e_x27_1048_ = v_arg_1070_;
goto v___jp_1047_;
}
}
}
}
}
else
{
lean_object* v_a_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1087_; 
lean_dec_ref(v_e_1041_);
v_a_1080_ = lean_ctor_get(v___x_1062_, 0);
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_1062_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1082_ = v___x_1062_;
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_a_1080_);
lean_dec(v___x_1062_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1085_; 
if (v_isShared_1083_ == 0)
{
v___x_1085_ = v___x_1082_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_a_1080_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
}
v___jp_1047_:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1049_ = lean_unsigned_to_nat(1u);
v___x_1050_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___redArg(v_e_x27_1048_, v___x_1049_);
lean_dec_ref(v_e_x27_1048_);
return v___x_1050_;
}
v___jp_1051_:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1053_ = lean_unsigned_to_nat(0u);
v___x_1054_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___redArg(v_e_x27_1052_, v___x_1053_);
lean_dec_ref(v_e_x27_1052_);
return v___x_1054_;
}
v___jp_1055_:
{
uint8_t v___x_1056_; 
v___x_1056_ = l_Lean_Expr_isProj(v_e_1041_);
if (v___x_1056_ == 0)
{
lean_object* v___x_1057_; lean_object* v___x_1058_; 
lean_dec_ref(v_e_1041_);
v___x_1057_ = ((lean_object*)(l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___redArg___closed__0));
v___x_1058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1057_);
return v___x_1058_;
}
else
{
lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1059_ = l_Lean_Expr_projExpr_x21(v_e_1041_);
v___x_1060_ = l_Lean_Expr_projIdx_x21(v_e_1041_);
lean_dec_ref(v_e_1041_);
v___x_1061_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___redArg(v___x_1059_, v___x_1060_);
lean_dec(v___x_1060_);
lean_dec_ref(v___x_1059_);
return v___x_1061_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_reduceProjs___lam__1___boxed(lean_object* v_e_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_){
_start:
{
lean_object* v_res_1094_; 
v_res_1094_ = l_Lean_Meta_PProdN_reduceProjs___lam__1(v_e_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_);
lean_dec(v___y_1092_);
lean_dec_ref(v___y_1091_);
lean_dec(v___y_1090_);
lean_dec_ref(v___y_1089_);
return v_res_1094_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3_spec__4___redArg(lean_object* v_a_1095_, lean_object* v_x_1096_){
_start:
{
if (lean_obj_tag(v_x_1096_) == 0)
{
lean_object* v___x_1097_; 
v___x_1097_ = lean_box(0);
return v___x_1097_;
}
else
{
lean_object* v_key_1098_; lean_object* v_value_1099_; lean_object* v_tail_1100_; uint8_t v___x_1101_; 
v_key_1098_ = lean_ctor_get(v_x_1096_, 0);
v_value_1099_ = lean_ctor_get(v_x_1096_, 1);
v_tail_1100_ = lean_ctor_get(v_x_1096_, 2);
v___x_1101_ = l_Lean_ExprStructEq_beq(v_key_1098_, v_a_1095_);
if (v___x_1101_ == 0)
{
v_x_1096_ = v_tail_1100_;
goto _start;
}
else
{
lean_object* v___x_1103_; 
lean_inc(v_value_1099_);
v___x_1103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1103_, 0, v_value_1099_);
return v___x_1103_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object* v_a_1104_, lean_object* v_x_1105_){
_start:
{
lean_object* v_res_1106_; 
v_res_1106_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3_spec__4___redArg(v_a_1104_, v_x_1105_);
lean_dec(v_x_1105_);
lean_dec_ref(v_a_1104_);
return v_res_1106_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3___redArg(lean_object* v_m_1107_, lean_object* v_a_1108_){
_start:
{
lean_object* v_buckets_1109_; lean_object* v___x_1110_; uint64_t v___x_1111_; uint64_t v___x_1112_; uint64_t v___x_1113_; uint64_t v_fold_1114_; uint64_t v___x_1115_; uint64_t v___x_1116_; uint64_t v___x_1117_; size_t v___x_1118_; size_t v___x_1119_; size_t v___x_1120_; size_t v___x_1121_; size_t v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; 
v_buckets_1109_ = lean_ctor_get(v_m_1107_, 1);
v___x_1110_ = lean_array_get_size(v_buckets_1109_);
v___x_1111_ = l_Lean_ExprStructEq_hash(v_a_1108_);
v___x_1112_ = 32ULL;
v___x_1113_ = lean_uint64_shift_right(v___x_1111_, v___x_1112_);
v_fold_1114_ = lean_uint64_xor(v___x_1111_, v___x_1113_);
v___x_1115_ = 16ULL;
v___x_1116_ = lean_uint64_shift_right(v_fold_1114_, v___x_1115_);
v___x_1117_ = lean_uint64_xor(v_fold_1114_, v___x_1116_);
v___x_1118_ = lean_uint64_to_usize(v___x_1117_);
v___x_1119_ = lean_usize_of_nat(v___x_1110_);
v___x_1120_ = ((size_t)1ULL);
v___x_1121_ = lean_usize_sub(v___x_1119_, v___x_1120_);
v___x_1122_ = lean_usize_land(v___x_1118_, v___x_1121_);
v___x_1123_ = lean_array_uget_borrowed(v_buckets_1109_, v___x_1122_);
v___x_1124_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3_spec__4___redArg(v_a_1108_, v___x_1123_);
return v___x_1124_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_m_1125_, lean_object* v_a_1126_){
_start:
{
lean_object* v_res_1127_; 
v_res_1127_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3___redArg(v_m_1125_, v_a_1126_);
lean_dec_ref(v_a_1126_);
lean_dec_ref(v_m_1125_);
return v_res_1127_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__12___redArg(lean_object* v_a_1128_, lean_object* v_b_1129_, lean_object* v_x_1130_){
_start:
{
if (lean_obj_tag(v_x_1130_) == 0)
{
lean_dec(v_b_1129_);
lean_dec_ref(v_a_1128_);
return v_x_1130_;
}
else
{
lean_object* v_key_1131_; lean_object* v_value_1132_; lean_object* v_tail_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1145_; 
v_key_1131_ = lean_ctor_get(v_x_1130_, 0);
v_value_1132_ = lean_ctor_get(v_x_1130_, 1);
v_tail_1133_ = lean_ctor_get(v_x_1130_, 2);
v_isSharedCheck_1145_ = !lean_is_exclusive(v_x_1130_);
if (v_isSharedCheck_1145_ == 0)
{
v___x_1135_ = v_x_1130_;
v_isShared_1136_ = v_isSharedCheck_1145_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_tail_1133_);
lean_inc(v_value_1132_);
lean_inc(v_key_1131_);
lean_dec(v_x_1130_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1145_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
uint8_t v___x_1137_; 
v___x_1137_ = l_Lean_ExprStructEq_beq(v_key_1131_, v_a_1128_);
if (v___x_1137_ == 0)
{
lean_object* v___x_1138_; lean_object* v___x_1140_; 
v___x_1138_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__12___redArg(v_a_1128_, v_b_1129_, v_tail_1133_);
if (v_isShared_1136_ == 0)
{
lean_ctor_set(v___x_1135_, 2, v___x_1138_);
v___x_1140_ = v___x_1135_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_key_1131_);
lean_ctor_set(v_reuseFailAlloc_1141_, 1, v_value_1132_);
lean_ctor_set(v_reuseFailAlloc_1141_, 2, v___x_1138_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
else
{
lean_object* v___x_1143_; 
lean_dec(v_value_1132_);
lean_dec(v_key_1131_);
if (v_isShared_1136_ == 0)
{
lean_ctor_set(v___x_1135_, 1, v_b_1129_);
lean_ctor_set(v___x_1135_, 0, v_a_1128_);
v___x_1143_ = v___x_1135_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v_a_1128_);
lean_ctor_set(v_reuseFailAlloc_1144_, 1, v_b_1129_);
lean_ctor_set(v_reuseFailAlloc_1144_, 2, v_tail_1133_);
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
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(lean_object* v_x_1146_, lean_object* v_x_1147_){
_start:
{
if (lean_obj_tag(v_x_1147_) == 0)
{
return v_x_1146_;
}
else
{
lean_object* v_key_1148_; lean_object* v_value_1149_; lean_object* v_tail_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1173_; 
v_key_1148_ = lean_ctor_get(v_x_1147_, 0);
v_value_1149_ = lean_ctor_get(v_x_1147_, 1);
v_tail_1150_ = lean_ctor_get(v_x_1147_, 2);
v_isSharedCheck_1173_ = !lean_is_exclusive(v_x_1147_);
if (v_isSharedCheck_1173_ == 0)
{
v___x_1152_ = v_x_1147_;
v_isShared_1153_ = v_isSharedCheck_1173_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_tail_1150_);
lean_inc(v_value_1149_);
lean_inc(v_key_1148_);
lean_dec(v_x_1147_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1173_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1154_; uint64_t v___x_1155_; uint64_t v___x_1156_; uint64_t v___x_1157_; uint64_t v_fold_1158_; uint64_t v___x_1159_; uint64_t v___x_1160_; uint64_t v___x_1161_; size_t v___x_1162_; size_t v___x_1163_; size_t v___x_1164_; size_t v___x_1165_; size_t v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1169_; 
v___x_1154_ = lean_array_get_size(v_x_1146_);
v___x_1155_ = l_Lean_ExprStructEq_hash(v_key_1148_);
v___x_1156_ = 32ULL;
v___x_1157_ = lean_uint64_shift_right(v___x_1155_, v___x_1156_);
v_fold_1158_ = lean_uint64_xor(v___x_1155_, v___x_1157_);
v___x_1159_ = 16ULL;
v___x_1160_ = lean_uint64_shift_right(v_fold_1158_, v___x_1159_);
v___x_1161_ = lean_uint64_xor(v_fold_1158_, v___x_1160_);
v___x_1162_ = lean_uint64_to_usize(v___x_1161_);
v___x_1163_ = lean_usize_of_nat(v___x_1154_);
v___x_1164_ = ((size_t)1ULL);
v___x_1165_ = lean_usize_sub(v___x_1163_, v___x_1164_);
v___x_1166_ = lean_usize_land(v___x_1162_, v___x_1165_);
v___x_1167_ = lean_array_uget_borrowed(v_x_1146_, v___x_1166_);
lean_inc(v___x_1167_);
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 2, v___x_1167_);
v___x_1169_ = v___x_1152_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v_key_1148_);
lean_ctor_set(v_reuseFailAlloc_1172_, 1, v_value_1149_);
lean_ctor_set(v_reuseFailAlloc_1172_, 2, v___x_1167_);
v___x_1169_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
lean_object* v___x_1170_; 
v___x_1170_ = lean_array_uset(v_x_1146_, v___x_1166_, v___x_1169_);
v_x_1146_ = v___x_1170_;
v_x_1147_ = v_tail_1150_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(lean_object* v_i_1174_, lean_object* v_source_1175_, lean_object* v_target_1176_){
_start:
{
lean_object* v___x_1177_; uint8_t v___x_1178_; 
v___x_1177_ = lean_array_get_size(v_source_1175_);
v___x_1178_ = lean_nat_dec_lt(v_i_1174_, v___x_1177_);
if (v___x_1178_ == 0)
{
lean_dec_ref(v_source_1175_);
lean_dec(v_i_1174_);
return v_target_1176_;
}
else
{
lean_object* v_es_1179_; lean_object* v___x_1180_; lean_object* v_source_1181_; lean_object* v_target_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; 
v_es_1179_ = lean_array_fget(v_source_1175_, v_i_1174_);
v___x_1180_ = lean_box(0);
v_source_1181_ = lean_array_fset(v_source_1175_, v_i_1174_, v___x_1180_);
v_target_1182_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_target_1176_, v_es_1179_);
v___x_1183_ = lean_unsigned_to_nat(1u);
v___x_1184_ = lean_nat_add(v_i_1174_, v___x_1183_);
lean_dec(v_i_1174_);
v_i_1174_ = v___x_1184_;
v_source_1175_ = v_source_1181_;
v_target_1176_ = v_target_1182_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11___redArg(lean_object* v_data_1186_){
_start:
{
lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v_nbuckets_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1187_ = lean_array_get_size(v_data_1186_);
v___x_1188_ = lean_unsigned_to_nat(2u);
v_nbuckets_1189_ = lean_nat_mul(v___x_1187_, v___x_1188_);
v___x_1190_ = lean_unsigned_to_nat(0u);
v___x_1191_ = lean_box(0);
v___x_1192_ = lean_mk_array(v_nbuckets_1189_, v___x_1191_);
v___x_1193_ = lean_array_propagate_mark(v_data_1186_, v___x_1192_);
v___x_1194_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v___x_1190_, v_data_1186_, v___x_1193_);
return v___x_1194_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__10___redArg(lean_object* v_a_1195_, lean_object* v_x_1196_){
_start:
{
if (lean_obj_tag(v_x_1196_) == 0)
{
uint8_t v___x_1197_; 
v___x_1197_ = 0;
return v___x_1197_;
}
else
{
lean_object* v_key_1198_; lean_object* v_tail_1199_; uint8_t v___x_1200_; 
v_key_1198_ = lean_ctor_get(v_x_1196_, 0);
v_tail_1199_ = lean_ctor_get(v_x_1196_, 2);
v___x_1200_ = l_Lean_ExprStructEq_beq(v_key_1198_, v_a_1195_);
if (v___x_1200_ == 0)
{
v_x_1196_ = v_tail_1199_;
goto _start;
}
else
{
return v___x_1200_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__10___redArg___boxed(lean_object* v_a_1202_, lean_object* v_x_1203_){
_start:
{
uint8_t v_res_1204_; lean_object* v_r_1205_; 
v_res_1204_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__10___redArg(v_a_1202_, v_x_1203_);
lean_dec(v_x_1203_);
lean_dec_ref(v_a_1202_);
v_r_1205_ = lean_box(v_res_1204_);
return v_r_1205_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6___redArg(lean_object* v_m_1206_, lean_object* v_a_1207_, lean_object* v_b_1208_){
_start:
{
lean_object* v_size_1209_; lean_object* v_buckets_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1253_; 
v_size_1209_ = lean_ctor_get(v_m_1206_, 0);
v_buckets_1210_ = lean_ctor_get(v_m_1206_, 1);
v_isSharedCheck_1253_ = !lean_is_exclusive(v_m_1206_);
if (v_isSharedCheck_1253_ == 0)
{
v___x_1212_ = v_m_1206_;
v_isShared_1213_ = v_isSharedCheck_1253_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_buckets_1210_);
lean_inc(v_size_1209_);
lean_dec(v_m_1206_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1253_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1214_; uint64_t v___x_1215_; uint64_t v___x_1216_; uint64_t v___x_1217_; uint64_t v_fold_1218_; uint64_t v___x_1219_; uint64_t v___x_1220_; uint64_t v___x_1221_; size_t v___x_1222_; size_t v___x_1223_; size_t v___x_1224_; size_t v___x_1225_; size_t v___x_1226_; lean_object* v_bkt_1227_; uint8_t v___x_1228_; 
v___x_1214_ = lean_array_get_size(v_buckets_1210_);
v___x_1215_ = l_Lean_ExprStructEq_hash(v_a_1207_);
v___x_1216_ = 32ULL;
v___x_1217_ = lean_uint64_shift_right(v___x_1215_, v___x_1216_);
v_fold_1218_ = lean_uint64_xor(v___x_1215_, v___x_1217_);
v___x_1219_ = 16ULL;
v___x_1220_ = lean_uint64_shift_right(v_fold_1218_, v___x_1219_);
v___x_1221_ = lean_uint64_xor(v_fold_1218_, v___x_1220_);
v___x_1222_ = lean_uint64_to_usize(v___x_1221_);
v___x_1223_ = lean_usize_of_nat(v___x_1214_);
v___x_1224_ = ((size_t)1ULL);
v___x_1225_ = lean_usize_sub(v___x_1223_, v___x_1224_);
v___x_1226_ = lean_usize_land(v___x_1222_, v___x_1225_);
v_bkt_1227_ = lean_array_uget_borrowed(v_buckets_1210_, v___x_1226_);
v___x_1228_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__10___redArg(v_a_1207_, v_bkt_1227_);
if (v___x_1228_ == 0)
{
lean_object* v___x_1229_; lean_object* v_size_x27_1230_; lean_object* v___x_1231_; lean_object* v_buckets_x27_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; uint8_t v___x_1238_; 
v___x_1229_ = lean_unsigned_to_nat(1u);
v_size_x27_1230_ = lean_nat_add(v_size_1209_, v___x_1229_);
lean_dec(v_size_1209_);
lean_inc(v_bkt_1227_);
v___x_1231_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1231_, 0, v_a_1207_);
lean_ctor_set(v___x_1231_, 1, v_b_1208_);
lean_ctor_set(v___x_1231_, 2, v_bkt_1227_);
v_buckets_x27_1232_ = lean_array_uset(v_buckets_1210_, v___x_1226_, v___x_1231_);
v___x_1233_ = lean_unsigned_to_nat(4u);
v___x_1234_ = lean_nat_mul(v_size_x27_1230_, v___x_1233_);
v___x_1235_ = lean_unsigned_to_nat(3u);
v___x_1236_ = lean_nat_div(v___x_1234_, v___x_1235_);
lean_dec(v___x_1234_);
v___x_1237_ = lean_array_get_size(v_buckets_x27_1232_);
v___x_1238_ = lean_nat_dec_le(v___x_1236_, v___x_1237_);
lean_dec(v___x_1236_);
if (v___x_1238_ == 0)
{
lean_object* v_val_1239_; lean_object* v___x_1241_; 
v_val_1239_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11___redArg(v_buckets_x27_1232_);
if (v_isShared_1213_ == 0)
{
lean_ctor_set(v___x_1212_, 1, v_val_1239_);
lean_ctor_set(v___x_1212_, 0, v_size_x27_1230_);
v___x_1241_ = v___x_1212_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v_size_x27_1230_);
lean_ctor_set(v_reuseFailAlloc_1242_, 1, v_val_1239_);
v___x_1241_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
return v___x_1241_;
}
}
else
{
lean_object* v___x_1244_; 
if (v_isShared_1213_ == 0)
{
lean_ctor_set(v___x_1212_, 1, v_buckets_x27_1232_);
lean_ctor_set(v___x_1212_, 0, v_size_x27_1230_);
v___x_1244_ = v___x_1212_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_size_x27_1230_);
lean_ctor_set(v_reuseFailAlloc_1245_, 1, v_buckets_x27_1232_);
v___x_1244_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
return v___x_1244_;
}
}
}
else
{
lean_object* v___x_1246_; lean_object* v_buckets_x27_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1251_; 
lean_inc(v_bkt_1227_);
v___x_1246_ = lean_box(0);
v_buckets_x27_1247_ = lean_array_uset(v_buckets_1210_, v___x_1226_, v___x_1246_);
v___x_1248_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__12___redArg(v_a_1207_, v_b_1208_, v_bkt_1227_);
v___x_1249_ = lean_array_uset(v_buckets_x27_1247_, v___x_1226_, v___x_1248_);
if (v_isShared_1213_ == 0)
{
lean_ctor_set(v___x_1212_, 1, v___x_1249_);
v___x_1251_ = v___x_1212_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v_size_1209_);
lean_ctor_set(v_reuseFailAlloc_1252_, 1, v___x_1249_);
v___x_1251_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
return v___x_1251_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__2(lean_object* v_a_1254_, lean_object* v_e_1255_, lean_object* v_a_1256_){
_start:
{
lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1258_ = lean_st_ref_take(v_a_1254_);
v___x_1259_ = lean_box(0);
v___x_1260_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6___redArg(v___x_1258_, v_e_1255_, v_a_1256_);
v___x_1261_ = lean_st_ref_put(v_a_1254_, v___x_1260_);
return v___x_1259_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__2___boxed(lean_object* v_a_1262_, lean_object* v_e_1263_, lean_object* v_a_1264_, lean_object* v___y_1265_){
_start:
{
lean_object* v_res_1266_; 
v_res_1266_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__2(v_a_1262_, v_e_1263_, v_a_1264_);
lean_dec(v_a_1262_);
return v_res_1266_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_1267_, lean_object* v_x_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_){
_start:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1274_ = lean_apply_1(v_x_1268_, lean_box(0));
v___x_1275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1275_, 0, v___x_1274_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_1276_, lean_object* v_x_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_){
_start:
{
lean_object* v_res_1283_; 
v_res_1283_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__0(v_00_u03b1_1276_, v_x_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
return v_res_1283_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; 
v___x_1284_ = lean_box(0);
v___x_1285_ = l_Lean_interruptExceptionId;
v___x_1286_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1286_, 0, v___x_1285_);
lean_ctor_set(v___x_1286_, 1, v___x_1284_);
return v___x_1286_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__8___redArg(){
_start:
{
lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1288_ = lean_obj_once(&l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__8___redArg___closed__0, &l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__8___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__8___redArg___closed__0);
v___x_1289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1289_, 0, v___x_1288_);
return v___x_1289_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__8___redArg___boxed(lean_object* v___y_1290_){
_start:
{
lean_object* v_res_1291_; 
v_res_1291_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__8___redArg();
return v_res_1291_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1297_ = l_Lean_maxRecDepthErrorMessage;
v___x_1298_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1298_, 0, v___x_1297_);
return v___x_1298_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1299_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__3);
v___x_1300_ = l_Lean_MessageData_ofFormat(v___x_1299_);
return v___x_1300_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; 
v___x_1301_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__4);
v___x_1302_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__2));
v___x_1303_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1303_, 0, v___x_1302_);
lean_ctor_set(v___x_1303_, 1, v___x_1301_);
return v___x_1303_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg(lean_object* v_ref_1304_){
_start:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1306_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__5);
v___x_1307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1307_, 0, v_ref_1304_);
lean_ctor_set(v___x_1307_, 1, v___x_1306_);
v___x_1308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1308_, 0, v___x_1307_);
return v___x_1308_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object* v_ref_1309_, lean_object* v___y_1310_){
_start:
{
lean_object* v_res_1311_; 
v_res_1311_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_1309_);
return v_res_1311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5___redArg(lean_object* v_x_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_){
_start:
{
lean_object* v___y_1320_; uint8_t v___y_1330_; lean_object* v___y_1331_; lean_object* v___y_1332_; uint8_t v___y_1333_; lean_object* v___y_1334_; uint16_t v___y_1335_; uint8_t v___y_1336_; lean_object* v_toCold_1341_; lean_object* v_currRecDepth_1342_; lean_object* v_ref_1343_; uint16_t v_optionFlags_1344_; uint8_t v_suppressElabErrors_1345_; uint8_t v_checkDeprecated_1346_; uint8_t v_isRecordingDeps_1347_; lean_object* v_maxRecDepth_1348_; lean_object* v_cancelTk_x3f_1349_; 
v_toCold_1341_ = lean_ctor_get(v___y_1316_, 0);
v_currRecDepth_1342_ = lean_ctor_get(v___y_1316_, 1);
v_ref_1343_ = lean_ctor_get(v___y_1316_, 2);
v_optionFlags_1344_ = lean_ctor_get_uint16(v___y_1316_, sizeof(void*)*3);
v_suppressElabErrors_1345_ = lean_ctor_get_uint8(v___y_1316_, sizeof(void*)*3 + 2);
v_checkDeprecated_1346_ = lean_ctor_get_uint8(v___y_1316_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1347_ = lean_ctor_get_uint8(v___y_1316_, sizeof(void*)*3 + 4);
v_maxRecDepth_1348_ = lean_ctor_get(v_toCold_1341_, 3);
v_cancelTk_x3f_1349_ = lean_ctor_get(v_toCold_1341_, 10);
if (lean_obj_tag(v_cancelTk_x3f_1349_) == 1)
{
lean_object* v_val_1355_; uint8_t v___x_1356_; 
v_val_1355_ = lean_ctor_get(v_cancelTk_x3f_1349_, 0);
v___x_1356_ = l_IO_CancelToken_isSet(v_val_1355_);
if (v___x_1356_ == 0)
{
goto v___jp_1350_;
}
else
{
lean_object* v___x_1357_; lean_object* v_a_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1365_; 
lean_dec_ref(v_x_1312_);
v___x_1357_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__8___redArg();
v_a_1358_ = lean_ctor_get(v___x_1357_, 0);
v_isSharedCheck_1365_ = !lean_is_exclusive(v___x_1357_);
if (v_isSharedCheck_1365_ == 0)
{
v___x_1360_ = v___x_1357_;
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_a_1358_);
lean_dec(v___x_1357_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v___x_1363_; 
if (v_isShared_1361_ == 0)
{
v___x_1363_ = v___x_1360_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v_a_1358_);
v___x_1363_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
return v___x_1363_;
}
}
}
}
else
{
goto v___jp_1350_;
}
v___jp_1319_:
{
if (lean_obj_tag(v___y_1320_) == 0)
{
return v___y_1320_;
}
else
{
lean_object* v_a_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1328_; 
v_a_1321_ = lean_ctor_get(v___y_1320_, 0);
v_isSharedCheck_1328_ = !lean_is_exclusive(v___y_1320_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1323_ = v___y_1320_;
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_a_1321_);
lean_dec(v___y_1320_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1326_; 
if (v_isShared_1324_ == 0)
{
v___x_1326_ = v___x_1323_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_a_1321_);
v___x_1326_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
return v___x_1326_;
}
}
}
}
v___jp_1329_:
{
lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___x_1337_ = lean_unsigned_to_nat(1u);
v___x_1338_ = lean_nat_add(v___y_1332_, v___x_1337_);
lean_inc_ref(v___y_1331_);
v___x_1339_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1339_, 0, v___y_1331_);
lean_ctor_set(v___x_1339_, 1, v___x_1338_);
lean_ctor_set(v___x_1339_, 2, v___y_1334_);
lean_ctor_set_uint16(v___x_1339_, sizeof(void*)*3, v___y_1335_);
lean_ctor_set_uint8(v___x_1339_, sizeof(void*)*3 + 2, v___y_1333_);
lean_ctor_set_uint8(v___x_1339_, sizeof(void*)*3 + 3, v___y_1336_);
lean_ctor_set_uint8(v___x_1339_, sizeof(void*)*3 + 4, v___y_1330_);
lean_inc(v___y_1317_);
lean_inc(v___y_1315_);
lean_inc_ref(v___y_1314_);
lean_inc(v___y_1313_);
v___x_1340_ = lean_apply_6(v_x_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___x_1339_, v___y_1317_, lean_box(0));
v___y_1320_ = v___x_1340_;
goto v___jp_1319_;
}
v___jp_1350_:
{
lean_object* v___x_1351_; uint8_t v___x_1352_; 
v___x_1351_ = lean_unsigned_to_nat(0u);
v___x_1352_ = lean_nat_dec_eq(v_maxRecDepth_1348_, v___x_1351_);
if (v___x_1352_ == 0)
{
uint8_t v___x_1353_; 
v___x_1353_ = lean_nat_dec_eq(v_currRecDepth_1342_, v_maxRecDepth_1348_);
if (v___x_1353_ == 0)
{
lean_inc(v_ref_1343_);
v___y_1330_ = v_isRecordingDeps_1347_;
v___y_1331_ = v_toCold_1341_;
v___y_1332_ = v_currRecDepth_1342_;
v___y_1333_ = v_suppressElabErrors_1345_;
v___y_1334_ = v_ref_1343_;
v___y_1335_ = v_optionFlags_1344_;
v___y_1336_ = v_checkDeprecated_1346_;
goto v___jp_1329_;
}
else
{
lean_object* v___x_1354_; 
lean_dec_ref(v_x_1312_);
lean_inc(v_ref_1343_);
v___x_1354_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_1343_);
v___y_1320_ = v___x_1354_;
goto v___jp_1319_;
}
}
else
{
lean_inc(v_ref_1343_);
v___y_1330_ = v_isRecordingDeps_1347_;
v___y_1331_ = v_toCold_1341_;
v___y_1332_ = v_currRecDepth_1342_;
v___y_1333_ = v_suppressElabErrors_1345_;
v___y_1334_ = v_ref_1343_;
v___y_1335_ = v_optionFlags_1344_;
v___y_1336_ = v_checkDeprecated_1346_;
goto v___jp_1329_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_x_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_){
_start:
{
lean_object* v_res_1373_; 
v_res_1373_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5___redArg(v_x_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_);
lean_dec(v___y_1371_);
lean_dec_ref(v___y_1370_);
lean_dec(v___y_1369_);
lean_dec_ref(v___y_1368_);
lean_dec(v___y_1367_);
return v_res_1373_;
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__1___closed__0(void){
_start:
{
lean_object* v___x_1375_; lean_object* v_dummy_1376_; 
v___x_1375_ = lean_box(0);
v_dummy_1376_ = l_Lean_Expr_sort___override(v___x_1375_);
return v_dummy_1376_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__1(lean_object* v_pre_1377_, lean_object* v_post_1378_, size_t v_sz_1379_, size_t v_i_1380_, lean_object* v_bs_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_){
_start:
{
uint8_t v___x_1388_; 
v___x_1388_ = lean_usize_dec_lt(v_i_1380_, v_sz_1379_);
if (v___x_1388_ == 0)
{
lean_object* v___x_1389_; 
lean_dec_ref(v_post_1378_);
lean_dec_ref(v_pre_1377_);
v___x_1389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1389_, 0, v_bs_1381_);
return v___x_1389_;
}
else
{
lean_object* v_v_1390_; lean_object* v___x_1391_; lean_object* v_bs_x27_1392_; lean_object* v___x_1393_; 
v_v_1390_ = lean_array_uget(v_bs_1381_, v_i_1380_);
v___x_1391_ = lean_unsigned_to_nat(0u);
v_bs_x27_1392_ = lean_array_uset(v_bs_1381_, v_i_1380_, v___x_1391_);
lean_inc_ref(v_post_1378_);
lean_inc_ref(v_pre_1377_);
v___x_1393_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1377_, v_post_1378_, v_v_1390_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_);
if (lean_obj_tag(v___x_1393_) == 0)
{
lean_object* v_a_1394_; size_t v___x_1395_; size_t v___x_1396_; lean_object* v___x_1397_; 
v_a_1394_ = lean_ctor_get(v___x_1393_, 0);
lean_inc(v_a_1394_);
lean_dec_ref_known(v___x_1393_, 1);
v___x_1395_ = ((size_t)1ULL);
v___x_1396_ = lean_usize_add(v_i_1380_, v___x_1395_);
v___x_1397_ = lean_array_uset(v_bs_x27_1392_, v_i_1380_, v_a_1394_);
v_i_1380_ = v___x_1396_;
v_bs_1381_ = v___x_1397_;
goto _start;
}
else
{
lean_object* v_a_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1406_; 
lean_dec_ref(v_bs_x27_1392_);
lean_dec_ref(v_post_1378_);
lean_dec_ref(v_pre_1377_);
v_a_1399_ = lean_ctor_get(v___x_1393_, 0);
v_isSharedCheck_1406_ = !lean_is_exclusive(v___x_1393_);
if (v_isSharedCheck_1406_ == 0)
{
v___x_1401_ = v___x_1393_;
v_isShared_1402_ = v_isSharedCheck_1406_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_a_1399_);
lean_dec(v___x_1393_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1406_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v___x_1404_; 
if (v_isShared_1402_ == 0)
{
v___x_1404_ = v___x_1401_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v_a_1399_);
v___x_1404_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
return v___x_1404_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__4(lean_object* v_pre_1407_, lean_object* v_post_1408_, lean_object* v_x_1409_, lean_object* v_x_1410_, lean_object* v_x_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_){
_start:
{
if (lean_obj_tag(v_x_1409_) == 5)
{
lean_object* v_fn_1418_; lean_object* v_arg_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; 
v_fn_1418_ = lean_ctor_get(v_x_1409_, 0);
lean_inc_ref(v_fn_1418_);
v_arg_1419_ = lean_ctor_get(v_x_1409_, 1);
lean_inc_ref(v_arg_1419_);
lean_dec_ref_known(v_x_1409_, 2);
v___x_1420_ = lean_array_set(v_x_1410_, v_x_1411_, v_arg_1419_);
v___x_1421_ = lean_unsigned_to_nat(1u);
v___x_1422_ = lean_nat_sub(v_x_1411_, v___x_1421_);
lean_dec(v_x_1411_);
v_x_1409_ = v_fn_1418_;
v_x_1410_ = v___x_1420_;
v_x_1411_ = v___x_1422_;
goto _start;
}
else
{
lean_object* v___x_1424_; 
lean_dec(v_x_1411_);
lean_inc_ref(v_post_1408_);
lean_inc_ref(v_pre_1407_);
v___x_1424_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1407_, v_post_1408_, v_x_1409_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_);
if (lean_obj_tag(v___x_1424_) == 0)
{
lean_object* v_a_1425_; size_t v_sz_1426_; size_t v___x_1427_; lean_object* v___x_1428_; 
v_a_1425_ = lean_ctor_get(v___x_1424_, 0);
lean_inc(v_a_1425_);
lean_dec_ref_known(v___x_1424_, 1);
v_sz_1426_ = lean_array_size(v_x_1410_);
v___x_1427_ = ((size_t)0ULL);
lean_inc_ref(v_post_1408_);
lean_inc_ref(v_pre_1407_);
v___x_1428_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__1(v_pre_1407_, v_post_1408_, v_sz_1426_, v___x_1427_, v_x_1410_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_);
if (lean_obj_tag(v___x_1428_) == 0)
{
lean_object* v_a_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; 
v_a_1429_ = lean_ctor_get(v___x_1428_, 0);
lean_inc(v_a_1429_);
lean_dec_ref_known(v___x_1428_, 1);
v___x_1430_ = l_Lean_mkAppN(v_a_1425_, v_a_1429_);
lean_dec(v_a_1429_);
v___x_1431_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1407_, v_post_1408_, v___x_1430_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_);
return v___x_1431_;
}
else
{
lean_object* v_a_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1439_; 
lean_dec(v_a_1425_);
lean_dec_ref(v_post_1408_);
lean_dec_ref(v_pre_1407_);
v_a_1432_ = lean_ctor_get(v___x_1428_, 0);
v_isSharedCheck_1439_ = !lean_is_exclusive(v___x_1428_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1434_ = v___x_1428_;
v_isShared_1435_ = v_isSharedCheck_1439_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_a_1432_);
lean_dec(v___x_1428_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1439_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___x_1437_; 
if (v_isShared_1435_ == 0)
{
v___x_1437_ = v___x_1434_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v_a_1432_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
return v___x_1437_;
}
}
}
}
else
{
lean_dec_ref(v_x_1410_);
lean_dec_ref(v_post_1408_);
lean_dec_ref(v_pre_1407_);
return v___x_1424_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__1(lean_object* v___x_1440_, lean_object* v_pre_1441_, lean_object* v_e_1442_, lean_object* v_post_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_){
_start:
{
lean_object* v___x_1450_; 
v___x_1450_ = l_Lean_Core_checkSystem(v___x_1440_, v___y_1447_, v___y_1448_);
if (lean_obj_tag(v___x_1450_) == 0)
{
lean_object* v___x_1451_; 
lean_dec_ref_known(v___x_1450_, 1);
lean_inc_ref(v_pre_1441_);
lean_inc(v___y_1448_);
lean_inc_ref(v___y_1447_);
lean_inc(v___y_1446_);
lean_inc_ref(v___y_1445_);
lean_inc_ref(v_e_1442_);
v___x_1451_ = lean_apply_6(v_pre_1441_, v_e_1442_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, lean_box(0));
if (lean_obj_tag(v___x_1451_) == 0)
{
lean_object* v_a_1452_; lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1567_; 
v_a_1452_ = lean_ctor_get(v___x_1451_, 0);
v_isSharedCheck_1567_ = !lean_is_exclusive(v___x_1451_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1454_ = v___x_1451_;
v_isShared_1455_ = v_isSharedCheck_1567_;
goto v_resetjp_1453_;
}
else
{
lean_inc(v_a_1452_);
lean_dec(v___x_1451_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1567_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
lean_object* v___y_1457_; 
switch(lean_obj_tag(v_a_1452_))
{
case 0:
{
lean_object* v_e_1557_; lean_object* v___x_1559_; 
lean_dec_ref(v_post_1443_);
lean_dec_ref(v_e_1442_);
lean_dec_ref(v_pre_1441_);
v_e_1557_ = lean_ctor_get(v_a_1452_, 0);
lean_inc_ref(v_e_1557_);
lean_dec_ref_known(v_a_1452_, 1);
if (v_isShared_1455_ == 0)
{
lean_ctor_set(v___x_1454_, 0, v_e_1557_);
v___x_1559_ = v___x_1454_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v_e_1557_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
case 1:
{
lean_object* v_e_1561_; lean_object* v___x_1562_; 
lean_del_object(v___x_1454_);
lean_dec_ref(v_e_1442_);
v_e_1561_ = lean_ctor_get(v_a_1452_, 0);
lean_inc_ref(v_e_1561_);
lean_dec_ref_known(v_a_1452_, 1);
lean_inc_ref(v_post_1443_);
lean_inc_ref(v_pre_1441_);
v___x_1562_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1441_, v_post_1443_, v_e_1561_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
if (lean_obj_tag(v___x_1562_) == 0)
{
lean_object* v_a_1563_; lean_object* v___x_1564_; 
v_a_1563_ = lean_ctor_get(v___x_1562_, 0);
lean_inc(v_a_1563_);
lean_dec_ref_known(v___x_1562_, 1);
v___x_1564_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1441_, v_post_1443_, v_a_1563_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
return v___x_1564_;
}
else
{
lean_dec_ref(v_post_1443_);
lean_dec_ref(v_pre_1441_);
return v___x_1562_;
}
}
default: 
{
lean_object* v_e_x3f_1565_; 
lean_del_object(v___x_1454_);
v_e_x3f_1565_ = lean_ctor_get(v_a_1452_, 0);
lean_inc(v_e_x3f_1565_);
lean_dec_ref_known(v_a_1452_, 1);
if (lean_obj_tag(v_e_x3f_1565_) == 0)
{
v___y_1457_ = v_e_1442_;
goto v___jp_1456_;
}
else
{
lean_object* v_val_1566_; 
lean_dec_ref(v_e_1442_);
v_val_1566_ = lean_ctor_get(v_e_x3f_1565_, 0);
lean_inc(v_val_1566_);
lean_dec_ref_known(v_e_x3f_1565_, 1);
v___y_1457_ = v_val_1566_;
goto v___jp_1456_;
}
}
}
v___jp_1456_:
{
switch(lean_obj_tag(v___y_1457_))
{
case 7:
{
lean_object* v_binderName_1458_; lean_object* v_binderType_1459_; lean_object* v_body_1460_; uint8_t v_binderInfo_1461_; lean_object* v___x_1462_; 
v_binderName_1458_ = lean_ctor_get(v___y_1457_, 0);
v_binderType_1459_ = lean_ctor_get(v___y_1457_, 1);
v_body_1460_ = lean_ctor_get(v___y_1457_, 2);
v_binderInfo_1461_ = lean_ctor_get_uint8(v___y_1457_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1459_);
lean_inc_ref(v_post_1443_);
lean_inc_ref(v_pre_1441_);
v___x_1462_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1441_, v_post_1443_, v_binderType_1459_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
if (lean_obj_tag(v___x_1462_) == 0)
{
lean_object* v_a_1463_; lean_object* v___x_1464_; 
v_a_1463_ = lean_ctor_get(v___x_1462_, 0);
lean_inc(v_a_1463_);
lean_dec_ref_known(v___x_1462_, 1);
lean_inc_ref(v_body_1460_);
lean_inc_ref(v_post_1443_);
lean_inc_ref(v_pre_1441_);
v___x_1464_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1441_, v_post_1443_, v_body_1460_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
if (lean_obj_tag(v___x_1464_) == 0)
{
lean_object* v_a_1465_; size_t v___x_1466_; size_t v___x_1467_; uint8_t v___x_1468_; 
v_a_1465_ = lean_ctor_get(v___x_1464_, 0);
lean_inc(v_a_1465_);
lean_dec_ref_known(v___x_1464_, 1);
v___x_1466_ = lean_ptr_addr(v_binderType_1459_);
v___x_1467_ = lean_ptr_addr(v_a_1463_);
v___x_1468_ = lean_usize_dec_eq(v___x_1466_, v___x_1467_);
if (v___x_1468_ == 0)
{
lean_object* v___x_1469_; lean_object* v___x_1470_; 
lean_inc(v_binderName_1458_);
lean_dec_ref_known(v___y_1457_, 3);
v___x_1469_ = l_Lean_Expr_forallE___override(v_binderName_1458_, v_a_1463_, v_a_1465_, v_binderInfo_1461_);
v___x_1470_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1441_, v_post_1443_, v___x_1469_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
return v___x_1470_;
}
else
{
size_t v___x_1471_; size_t v___x_1472_; uint8_t v___x_1473_; 
v___x_1471_ = lean_ptr_addr(v_body_1460_);
v___x_1472_ = lean_ptr_addr(v_a_1465_);
v___x_1473_ = lean_usize_dec_eq(v___x_1471_, v___x_1472_);
if (v___x_1473_ == 0)
{
lean_object* v___x_1474_; lean_object* v___x_1475_; 
lean_inc(v_binderName_1458_);
lean_dec_ref_known(v___y_1457_, 3);
v___x_1474_ = l_Lean_Expr_forallE___override(v_binderName_1458_, v_a_1463_, v_a_1465_, v_binderInfo_1461_);
v___x_1475_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1441_, v_post_1443_, v___x_1474_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
return v___x_1475_;
}
else
{
uint8_t v___x_1476_; 
v___x_1476_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1461_, v_binderInfo_1461_);
if (v___x_1476_ == 0)
{
lean_object* v___x_1477_; lean_object* v___x_1478_; 
lean_inc(v_binderName_1458_);
lean_dec_ref_known(v___y_1457_, 3);
v___x_1477_ = l_Lean_Expr_forallE___override(v_binderName_1458_, v_a_1463_, v_a_1465_, v_binderInfo_1461_);
v___x_1478_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1441_, v_post_1443_, v___x_1477_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
return v___x_1478_;
}
else
{
lean_object* v___x_1479_; 
lean_dec(v_a_1465_);
lean_dec(v_a_1463_);
v___x_1479_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1441_, v_post_1443_, v___y_1457_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
return v___x_1479_;
}
}
}
}
else
{
lean_dec(v_a_1463_);
lean_dec_ref_known(v___y_1457_, 3);
lean_dec_ref(v_post_1443_);
lean_dec_ref(v_pre_1441_);
return v___x_1464_;
}
}
else
{
lean_dec_ref_known(v___y_1457_, 3);
lean_dec_ref(v_post_1443_);
lean_dec_ref(v_pre_1441_);
return v___x_1462_;
}
}
case 6:
{
lean_object* v_binderName_1480_; lean_object* v_binderType_1481_; lean_object* v_body_1482_; uint8_t v_binderInfo_1483_; lean_object* v___x_1484_; 
v_binderName_1480_ = lean_ctor_get(v___y_1457_, 0);
v_binderType_1481_ = lean_ctor_get(v___y_1457_, 1);
v_body_1482_ = lean_ctor_get(v___y_1457_, 2);
v_binderInfo_1483_ = lean_ctor_get_uint8(v___y_1457_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1481_);
lean_inc_ref(v_post_1443_);
lean_inc_ref(v_pre_1441_);
v___x_1484_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1441_, v_post_1443_, v_binderType_1481_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
if (lean_obj_tag(v___x_1484_) == 0)
{
lean_object* v_a_1485_; lean_object* v___x_1486_; 
v_a_1485_ = lean_ctor_get(v___x_1484_, 0);
lean_inc(v_a_1485_);
lean_dec_ref_known(v___x_1484_, 1);
lean_inc_ref(v_body_1482_);
lean_inc_ref(v_post_1443_);
lean_inc_ref(v_pre_1441_);
v___x_1486_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1441_, v_post_1443_, v_body_1482_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
if (lean_obj_tag(v___x_1486_) == 0)
{
lean_object* v_a_1487_; size_t v___x_1488_; size_t v___x_1489_; uint8_t v___x_1490_; 
v_a_1487_ = lean_ctor_get(v___x_1486_, 0);
lean_inc(v_a_1487_);
lean_dec_ref_known(v___x_1486_, 1);
v___x_1488_ = lean_ptr_addr(v_binderType_1481_);
v___x_1489_ = lean_ptr_addr(v_a_1485_);
v___x_1490_ = lean_usize_dec_eq(v___x_1488_, v___x_1489_);
if (v___x_1490_ == 0)
{
lean_object* v___x_1491_; lean_object* v___x_1492_; 
lean_inc(v_binderName_1480_);
lean_dec_ref_known(v___y_1457_, 3);
v___x_1491_ = l_Lean_Expr_lam___override(v_binderName_1480_, v_a_1485_, v_a_1487_, v_binderInfo_1483_);
v___x_1492_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1441_, v_post_1443_, v___x_1491_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
return v___x_1492_;
}
else
{
size_t v___x_1493_; size_t v___x_1494_; uint8_t v___x_1495_; 
v___x_1493_ = lean_ptr_addr(v_body_1482_);
v___x_1494_ = lean_ptr_addr(v_a_1487_);
v___x_1495_ = lean_usize_dec_eq(v___x_1493_, v___x_1494_);
if (v___x_1495_ == 0)
{
lean_object* v___x_1496_; lean_object* v___x_1497_; 
lean_inc(v_binderName_1480_);
lean_dec_ref_known(v___y_1457_, 3);
v___x_1496_ = l_Lean_Expr_lam___override(v_binderName_1480_, v_a_1485_, v_a_1487_, v_binderInfo_1483_);
v___x_1497_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1441_, v_post_1443_, v___x_1496_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
return v___x_1497_;
}
else
{
uint8_t v___x_1498_; 
v___x_1498_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1483_, v_binderInfo_1483_);
if (v___x_1498_ == 0)
{
lean_object* v___x_1499_; lean_object* v___x_1500_; 
lean_inc(v_binderName_1480_);
lean_dec_ref_known(v___y_1457_, 3);
v___x_1499_ = l_Lean_Expr_lam___override(v_binderName_1480_, v_a_1485_, v_a_1487_, v_binderInfo_1483_);
v___x_1500_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1441_, v_post_1443_, v___x_1499_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
return v___x_1500_;
}
else
{
lean_object* v___x_1501_; 
lean_dec(v_a_1487_);
lean_dec(v_a_1485_);
v___x_1501_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1441_, v_post_1443_, v___y_1457_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
return v___x_1501_;
}
}
}
}
else
{
lean_dec(v_a_1485_);
lean_dec_ref_known(v___y_1457_, 3);
lean_dec_ref(v_post_1443_);
lean_dec_ref(v_pre_1441_);
return v___x_1486_;
}
}
else
{
lean_dec_ref_known(v___y_1457_, 3);
lean_dec_ref(v_post_1443_);
lean_dec_ref(v_pre_1441_);
return v___x_1484_;
}
}
case 8:
{
lean_object* v_declName_1502_; lean_object* v_type_1503_; lean_object* v_value_1504_; lean_object* v_body_1505_; uint8_t v_nondep_1506_; lean_object* v___x_1507_; 
v_declName_1502_ = lean_ctor_get(v___y_1457_, 0);
v_type_1503_ = lean_ctor_get(v___y_1457_, 1);
v_value_1504_ = lean_ctor_get(v___y_1457_, 2);
v_body_1505_ = lean_ctor_get(v___y_1457_, 3);
v_nondep_1506_ = lean_ctor_get_uint8(v___y_1457_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_1503_);
lean_inc_ref(v_post_1443_);
lean_inc_ref(v_pre_1441_);
v___x_1507_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1441_, v_post_1443_, v_type_1503_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
if (lean_obj_tag(v___x_1507_) == 0)
{
lean_object* v_a_1508_; lean_object* v___x_1509_; 
v_a_1508_ = lean_ctor_get(v___x_1507_, 0);
lean_inc(v_a_1508_);
lean_dec_ref_known(v___x_1507_, 1);
lean_inc_ref(v_value_1504_);
lean_inc_ref(v_post_1443_);
lean_inc_ref(v_pre_1441_);
v___x_1509_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1441_, v_post_1443_, v_value_1504_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
if (lean_obj_tag(v___x_1509_) == 0)
{
lean_object* v_a_1510_; lean_object* v___x_1511_; 
v_a_1510_ = lean_ctor_get(v___x_1509_, 0);
lean_inc(v_a_1510_);
lean_dec_ref_known(v___x_1509_, 1);
lean_inc_ref(v_body_1505_);
lean_inc_ref(v_post_1443_);
lean_inc_ref(v_pre_1441_);
v___x_1511_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1441_, v_post_1443_, v_body_1505_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
if (lean_obj_tag(v___x_1511_) == 0)
{
lean_object* v_a_1512_; size_t v___x_1513_; size_t v___x_1514_; uint8_t v___x_1515_; 
v_a_1512_ = lean_ctor_get(v___x_1511_, 0);
lean_inc(v_a_1512_);
lean_dec_ref_known(v___x_1511_, 1);
v___x_1513_ = lean_ptr_addr(v_type_1503_);
v___x_1514_ = lean_ptr_addr(v_a_1508_);
v___x_1515_ = lean_usize_dec_eq(v___x_1513_, v___x_1514_);
if (v___x_1515_ == 0)
{
lean_object* v___x_1516_; lean_object* v___x_1517_; 
lean_inc(v_declName_1502_);
lean_dec_ref_known(v___y_1457_, 4);
v___x_1516_ = l_Lean_Expr_letE___override(v_declName_1502_, v_a_1508_, v_a_1510_, v_a_1512_, v_nondep_1506_);
v___x_1517_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1441_, v_post_1443_, v___x_1516_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
return v___x_1517_;
}
else
{
size_t v___x_1518_; size_t v___x_1519_; uint8_t v___x_1520_; 
v___x_1518_ = lean_ptr_addr(v_value_1504_);
v___x_1519_ = lean_ptr_addr(v_a_1510_);
v___x_1520_ = lean_usize_dec_eq(v___x_1518_, v___x_1519_);
if (v___x_1520_ == 0)
{
lean_object* v___x_1521_; lean_object* v___x_1522_; 
lean_inc(v_declName_1502_);
lean_dec_ref_known(v___y_1457_, 4);
v___x_1521_ = l_Lean_Expr_letE___override(v_declName_1502_, v_a_1508_, v_a_1510_, v_a_1512_, v_nondep_1506_);
v___x_1522_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1441_, v_post_1443_, v___x_1521_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
return v___x_1522_;
}
else
{
size_t v___x_1523_; size_t v___x_1524_; uint8_t v___x_1525_; 
v___x_1523_ = lean_ptr_addr(v_body_1505_);
v___x_1524_ = lean_ptr_addr(v_a_1512_);
v___x_1525_ = lean_usize_dec_eq(v___x_1523_, v___x_1524_);
if (v___x_1525_ == 0)
{
lean_object* v___x_1526_; lean_object* v___x_1527_; 
lean_inc(v_declName_1502_);
lean_dec_ref_known(v___y_1457_, 4);
v___x_1526_ = l_Lean_Expr_letE___override(v_declName_1502_, v_a_1508_, v_a_1510_, v_a_1512_, v_nondep_1506_);
v___x_1527_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1441_, v_post_1443_, v___x_1526_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
return v___x_1527_;
}
else
{
lean_object* v___x_1528_; 
lean_dec(v_a_1512_);
lean_dec(v_a_1510_);
lean_dec(v_a_1508_);
v___x_1528_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1441_, v_post_1443_, v___y_1457_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
return v___x_1528_;
}
}
}
}
else
{
lean_dec(v_a_1510_);
lean_dec(v_a_1508_);
lean_dec_ref_known(v___y_1457_, 4);
lean_dec_ref(v_post_1443_);
lean_dec_ref(v_pre_1441_);
return v___x_1511_;
}
}
else
{
lean_dec(v_a_1508_);
lean_dec_ref_known(v___y_1457_, 4);
lean_dec_ref(v_post_1443_);
lean_dec_ref(v_pre_1441_);
return v___x_1509_;
}
}
else
{
lean_dec_ref_known(v___y_1457_, 4);
lean_dec_ref(v_post_1443_);
lean_dec_ref(v_pre_1441_);
return v___x_1507_;
}
}
case 5:
{
lean_object* v_dummy_1529_; lean_object* v_nargs_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; 
v_dummy_1529_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__1___closed__0);
v_nargs_1530_ = l_Lean_Expr_getAppNumArgs(v___y_1457_);
lean_inc(v_nargs_1530_);
v___x_1531_ = lean_mk_array(v_nargs_1530_, v_dummy_1529_);
v___x_1532_ = lean_unsigned_to_nat(1u);
v___x_1533_ = lean_nat_sub(v_nargs_1530_, v___x_1532_);
lean_dec(v_nargs_1530_);
v___x_1534_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__4(v_pre_1441_, v_post_1443_, v___y_1457_, v___x_1531_, v___x_1533_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
return v___x_1534_;
}
case 10:
{
lean_object* v_data_1535_; lean_object* v_expr_1536_; lean_object* v___x_1537_; 
v_data_1535_ = lean_ctor_get(v___y_1457_, 0);
v_expr_1536_ = lean_ctor_get(v___y_1457_, 1);
lean_inc_ref(v_expr_1536_);
lean_inc_ref(v_post_1443_);
lean_inc_ref(v_pre_1441_);
v___x_1537_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1441_, v_post_1443_, v_expr_1536_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
if (lean_obj_tag(v___x_1537_) == 0)
{
lean_object* v_a_1538_; size_t v___x_1539_; size_t v___x_1540_; uint8_t v___x_1541_; 
v_a_1538_ = lean_ctor_get(v___x_1537_, 0);
lean_inc(v_a_1538_);
lean_dec_ref_known(v___x_1537_, 1);
v___x_1539_ = lean_ptr_addr(v_expr_1536_);
v___x_1540_ = lean_ptr_addr(v_a_1538_);
v___x_1541_ = lean_usize_dec_eq(v___x_1539_, v___x_1540_);
if (v___x_1541_ == 0)
{
lean_object* v___x_1542_; lean_object* v___x_1543_; 
lean_inc(v_data_1535_);
lean_dec_ref_known(v___y_1457_, 2);
v___x_1542_ = l_Lean_Expr_mdata___override(v_data_1535_, v_a_1538_);
v___x_1543_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1441_, v_post_1443_, v___x_1542_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
return v___x_1543_;
}
else
{
lean_object* v___x_1544_; 
lean_dec(v_a_1538_);
v___x_1544_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1441_, v_post_1443_, v___y_1457_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
return v___x_1544_;
}
}
else
{
lean_dec_ref_known(v___y_1457_, 2);
lean_dec_ref(v_post_1443_);
lean_dec_ref(v_pre_1441_);
return v___x_1537_;
}
}
case 11:
{
lean_object* v_typeName_1545_; lean_object* v_idx_1546_; lean_object* v_struct_1547_; lean_object* v___x_1548_; 
v_typeName_1545_ = lean_ctor_get(v___y_1457_, 0);
v_idx_1546_ = lean_ctor_get(v___y_1457_, 1);
v_struct_1547_ = lean_ctor_get(v___y_1457_, 2);
lean_inc_ref(v_struct_1547_);
lean_inc_ref(v_post_1443_);
lean_inc_ref(v_pre_1441_);
v___x_1548_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1441_, v_post_1443_, v_struct_1547_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
if (lean_obj_tag(v___x_1548_) == 0)
{
lean_object* v_a_1549_; size_t v___x_1550_; size_t v___x_1551_; uint8_t v___x_1552_; 
v_a_1549_ = lean_ctor_get(v___x_1548_, 0);
lean_inc(v_a_1549_);
lean_dec_ref_known(v___x_1548_, 1);
v___x_1550_ = lean_ptr_addr(v_struct_1547_);
v___x_1551_ = lean_ptr_addr(v_a_1549_);
v___x_1552_ = lean_usize_dec_eq(v___x_1550_, v___x_1551_);
if (v___x_1552_ == 0)
{
lean_object* v___x_1553_; lean_object* v___x_1554_; 
lean_inc(v_idx_1546_);
lean_inc(v_typeName_1545_);
lean_dec_ref_known(v___y_1457_, 3);
v___x_1553_ = l_Lean_Expr_proj___override(v_typeName_1545_, v_idx_1546_, v_a_1549_);
v___x_1554_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1441_, v_post_1443_, v___x_1553_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
return v___x_1554_;
}
else
{
lean_object* v___x_1555_; 
lean_dec(v_a_1549_);
v___x_1555_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1441_, v_post_1443_, v___y_1457_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
return v___x_1555_;
}
}
else
{
lean_dec_ref_known(v___y_1457_, 3);
lean_dec_ref(v_post_1443_);
lean_dec_ref(v_pre_1441_);
return v___x_1548_;
}
}
default: 
{
lean_object* v___x_1556_; 
v___x_1556_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1441_, v_post_1443_, v___y_1457_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
return v___x_1556_;
}
}
}
}
}
else
{
lean_object* v_a_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1575_; 
lean_dec_ref(v_post_1443_);
lean_dec_ref(v_e_1442_);
lean_dec_ref(v_pre_1441_);
v_a_1568_ = lean_ctor_get(v___x_1451_, 0);
v_isSharedCheck_1575_ = !lean_is_exclusive(v___x_1451_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1570_ = v___x_1451_;
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_a_1568_);
lean_dec(v___x_1451_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v___x_1573_; 
if (v_isShared_1571_ == 0)
{
v___x_1573_ = v___x_1570_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v_a_1568_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
return v___x_1573_;
}
}
}
}
else
{
lean_object* v_a_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1583_; 
lean_dec_ref(v_post_1443_);
lean_dec_ref(v_e_1442_);
lean_dec_ref(v_pre_1441_);
v_a_1576_ = lean_ctor_get(v___x_1450_, 0);
v_isSharedCheck_1583_ = !lean_is_exclusive(v___x_1450_);
if (v_isSharedCheck_1583_ == 0)
{
v___x_1578_ = v___x_1450_;
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_a_1576_);
lean_dec(v___x_1450_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___x_1581_; 
if (v_isShared_1579_ == 0)
{
v___x_1581_ = v___x_1578_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v_a_1576_);
v___x_1581_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
return v___x_1581_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__1___boxed(lean_object* v___x_1584_, lean_object* v_pre_1585_, lean_object* v_e_1586_, lean_object* v_post_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_){
_start:
{
lean_object* v_res_1594_; 
v_res_1594_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__1(v___x_1584_, v_pre_1585_, v_e_1586_, v_post_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_);
lean_dec(v___y_1592_);
lean_dec_ref(v___y_1591_);
lean_dec(v___y_1590_);
lean_dec_ref(v___y_1589_);
lean_dec(v___y_1588_);
return v_res_1594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(lean_object* v_pre_1595_, lean_object* v_post_1596_, lean_object* v_e_1597_, lean_object* v_a_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_){
_start:
{
lean_object* v___x_1604_; lean_object* v___x_1605_; 
lean_inc(v_a_1598_);
v___x_1604_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1604_, 0, lean_box(0));
lean_closure_set(v___x_1604_, 1, lean_box(0));
lean_closure_set(v___x_1604_, 2, v_a_1598_);
v___x_1605_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__0(lean_box(0), v___x_1604_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_);
if (lean_obj_tag(v___x_1605_) == 0)
{
lean_object* v_a_1606_; lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1637_; 
v_a_1606_ = lean_ctor_get(v___x_1605_, 0);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1605_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1608_ = v___x_1605_;
v_isShared_1609_ = v_isSharedCheck_1637_;
goto v_resetjp_1607_;
}
else
{
lean_inc(v_a_1606_);
lean_dec(v___x_1605_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1637_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
lean_object* v___x_1610_; 
v___x_1610_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3___redArg(v_a_1606_, v_e_1597_);
lean_dec(v_a_1606_);
if (lean_obj_tag(v___x_1610_) == 0)
{
lean_object* v___x_1611_; lean_object* v___f_1612_; lean_object* v___x_1613_; 
lean_del_object(v___x_1608_);
v___x_1611_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___closed__0));
lean_inc_ref(v_e_1597_);
v___f_1612_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__1___boxed), 10, 4);
lean_closure_set(v___f_1612_, 0, v___x_1611_);
lean_closure_set(v___f_1612_, 1, v_pre_1595_);
lean_closure_set(v___f_1612_, 2, v_e_1597_);
lean_closure_set(v___f_1612_, 3, v_post_1596_);
v___x_1613_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5___redArg(v___f_1612_, v_a_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_);
if (lean_obj_tag(v___x_1613_) == 0)
{
lean_object* v_a_1614_; lean_object* v___f_1615_; lean_object* v___x_1616_; 
v_a_1614_ = lean_ctor_get(v___x_1613_, 0);
lean_inc_n(v_a_1614_, 2);
lean_dec_ref_known(v___x_1613_, 1);
lean_inc(v_a_1598_);
v___f_1615_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1615_, 0, v_a_1598_);
lean_closure_set(v___f_1615_, 1, v_e_1597_);
lean_closure_set(v___f_1615_, 2, v_a_1614_);
v___x_1616_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__0(lean_box(0), v___f_1615_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_);
if (lean_obj_tag(v___x_1616_) == 0)
{
lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1623_; 
v_isSharedCheck_1623_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1623_ == 0)
{
lean_object* v_unused_1624_; 
v_unused_1624_ = lean_ctor_get(v___x_1616_, 0);
lean_dec(v_unused_1624_);
v___x_1618_ = v___x_1616_;
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
else
{
lean_dec(v___x_1616_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___x_1621_; 
if (v_isShared_1619_ == 0)
{
lean_ctor_set(v___x_1618_, 0, v_a_1614_);
v___x_1621_ = v___x_1618_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v_a_1614_);
v___x_1621_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
return v___x_1621_;
}
}
}
else
{
lean_object* v_a_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1632_; 
lean_dec(v_a_1614_);
v_a_1625_ = lean_ctor_get(v___x_1616_, 0);
v_isSharedCheck_1632_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1632_ == 0)
{
v___x_1627_ = v___x_1616_;
v_isShared_1628_ = v_isSharedCheck_1632_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_a_1625_);
lean_dec(v___x_1616_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1632_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v___x_1630_; 
if (v_isShared_1628_ == 0)
{
v___x_1630_ = v___x_1627_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v_a_1625_);
v___x_1630_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
return v___x_1630_;
}
}
}
}
else
{
lean_dec_ref(v_e_1597_);
return v___x_1613_;
}
}
else
{
lean_object* v_val_1633_; lean_object* v___x_1635_; 
lean_dec_ref(v_e_1597_);
lean_dec_ref(v_post_1596_);
lean_dec_ref(v_pre_1595_);
v_val_1633_ = lean_ctor_get(v___x_1610_, 0);
lean_inc(v_val_1633_);
lean_dec_ref_known(v___x_1610_, 1);
if (v_isShared_1609_ == 0)
{
lean_ctor_set(v___x_1608_, 0, v_val_1633_);
v___x_1635_ = v___x_1608_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_val_1633_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
return v___x_1635_;
}
}
}
}
else
{
lean_object* v_a_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1645_; 
lean_dec_ref(v_e_1597_);
lean_dec_ref(v_post_1596_);
lean_dec_ref(v_pre_1595_);
v_a_1638_ = lean_ctor_get(v___x_1605_, 0);
v_isSharedCheck_1645_ = !lean_is_exclusive(v___x_1605_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1640_ = v___x_1605_;
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_a_1638_);
lean_dec(v___x_1605_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1643_; 
if (v_isShared_1641_ == 0)
{
v___x_1643_ = v___x_1640_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_a_1638_);
v___x_1643_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
return v___x_1643_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(lean_object* v_pre_1646_, lean_object* v_post_1647_, lean_object* v_e_1648_, lean_object* v_a_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_){
_start:
{
lean_object* v___x_1655_; 
lean_inc_ref(v_post_1647_);
lean_inc(v___y_1653_);
lean_inc_ref(v___y_1652_);
lean_inc(v___y_1651_);
lean_inc_ref(v___y_1650_);
lean_inc_ref(v_e_1648_);
v___x_1655_ = lean_apply_6(v_post_1647_, v_e_1648_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_, lean_box(0));
if (lean_obj_tag(v___x_1655_) == 0)
{
lean_object* v_a_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1674_; 
v_a_1656_ = lean_ctor_get(v___x_1655_, 0);
v_isSharedCheck_1674_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1674_ == 0)
{
v___x_1658_ = v___x_1655_;
v_isShared_1659_ = v_isSharedCheck_1674_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_a_1656_);
lean_dec(v___x_1655_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1674_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
switch(lean_obj_tag(v_a_1656_))
{
case 0:
{
lean_object* v_e_1660_; lean_object* v___x_1662_; 
lean_dec_ref(v_e_1648_);
lean_dec_ref(v_post_1647_);
lean_dec_ref(v_pre_1646_);
v_e_1660_ = lean_ctor_get(v_a_1656_, 0);
lean_inc_ref(v_e_1660_);
lean_dec_ref_known(v_a_1656_, 1);
if (v_isShared_1659_ == 0)
{
lean_ctor_set(v___x_1658_, 0, v_e_1660_);
v___x_1662_ = v___x_1658_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v_e_1660_);
v___x_1662_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
return v___x_1662_;
}
}
case 1:
{
lean_object* v_e_1664_; lean_object* v___x_1665_; 
lean_del_object(v___x_1658_);
lean_dec_ref(v_e_1648_);
v_e_1664_ = lean_ctor_get(v_a_1656_, 0);
lean_inc_ref(v_e_1664_);
lean_dec_ref_known(v_a_1656_, 1);
v___x_1665_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1646_, v_post_1647_, v_e_1664_, v_a_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_);
return v___x_1665_;
}
default: 
{
lean_object* v_e_x3f_1666_; 
lean_dec_ref(v_post_1647_);
lean_dec_ref(v_pre_1646_);
v_e_x3f_1666_ = lean_ctor_get(v_a_1656_, 0);
lean_inc(v_e_x3f_1666_);
lean_dec_ref_known(v_a_1656_, 1);
if (lean_obj_tag(v_e_x3f_1666_) == 0)
{
lean_object* v___x_1668_; 
if (v_isShared_1659_ == 0)
{
lean_ctor_set(v___x_1658_, 0, v_e_1648_);
v___x_1668_ = v___x_1658_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v_e_1648_);
v___x_1668_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
return v___x_1668_;
}
}
else
{
lean_object* v_val_1670_; lean_object* v___x_1672_; 
lean_dec_ref(v_e_1648_);
v_val_1670_ = lean_ctor_get(v_e_x3f_1666_, 0);
lean_inc(v_val_1670_);
lean_dec_ref_known(v_e_x3f_1666_, 1);
if (v_isShared_1659_ == 0)
{
lean_ctor_set(v___x_1658_, 0, v_val_1670_);
v___x_1672_ = v___x_1658_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v_val_1670_);
v___x_1672_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
return v___x_1672_;
}
}
}
}
}
}
else
{
lean_object* v_a_1675_; lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1682_; 
lean_dec_ref(v_e_1648_);
lean_dec_ref(v_post_1647_);
lean_dec_ref(v_pre_1646_);
v_a_1675_ = lean_ctor_get(v___x_1655_, 0);
v_isSharedCheck_1682_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1682_ == 0)
{
v___x_1677_ = v___x_1655_;
v_isShared_1678_ = v_isSharedCheck_1682_;
goto v_resetjp_1676_;
}
else
{
lean_inc(v_a_1675_);
lean_dec(v___x_1655_);
v___x_1677_ = lean_box(0);
v_isShared_1678_ = v_isSharedCheck_1682_;
goto v_resetjp_1676_;
}
v_resetjp_1676_:
{
lean_object* v___x_1680_; 
if (v_isShared_1678_ == 0)
{
v___x_1680_ = v___x_1677_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v_a_1675_);
v___x_1680_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
return v___x_1680_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_1683_, lean_object* v_post_1684_, lean_object* v_e_1685_, lean_object* v_a_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_){
_start:
{
lean_object* v_res_1692_; 
v_res_1692_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1683_, v_post_1684_, v_e_1685_, v_a_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
lean_dec(v___y_1690_);
lean_dec_ref(v___y_1689_);
lean_dec(v___y_1688_);
lean_dec_ref(v___y_1687_);
lean_dec(v_a_1686_);
return v_res_1692_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_1693_, lean_object* v_post_1694_, lean_object* v_sz_1695_, lean_object* v_i_1696_, lean_object* v_bs_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_){
_start:
{
size_t v_sz_boxed_1704_; size_t v_i_boxed_1705_; lean_object* v_res_1706_; 
v_sz_boxed_1704_ = lean_unbox_usize(v_sz_1695_);
lean_dec(v_sz_1695_);
v_i_boxed_1705_ = lean_unbox_usize(v_i_1696_);
lean_dec(v_i_1696_);
v_res_1706_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__1(v_pre_1693_, v_post_1694_, v_sz_boxed_1704_, v_i_boxed_1705_, v_bs_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1701_);
lean_dec(v___y_1700_);
lean_dec_ref(v___y_1699_);
lean_dec(v___y_1698_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__4___boxed(lean_object* v_pre_1707_, lean_object* v_post_1708_, lean_object* v_x_1709_, lean_object* v_x_1710_, lean_object* v_x_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_){
_start:
{
lean_object* v_res_1718_; 
v_res_1718_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__4(v_pre_1707_, v_post_1708_, v_x_1709_, v_x_1710_, v_x_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
lean_dec(v___y_1714_);
lean_dec_ref(v___y_1713_);
lean_dec(v___y_1712_);
return v_res_1718_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___boxed(lean_object* v_pre_1719_, lean_object* v_post_1720_, lean_object* v_e_1721_, lean_object* v_a_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_){
_start:
{
lean_object* v_res_1728_; 
v_res_1728_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1719_, v_post_1720_, v_e_1721_, v_a_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_);
lean_dec(v___y_1726_);
lean_dec_ref(v___y_1725_);
lean_dec(v___y_1724_);
lean_dec_ref(v___y_1723_);
lean_dec(v_a_1722_);
return v_res_1728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___lam__0(lean_object* v_00_u03b1_1729_, lean_object* v_x_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_){
_start:
{
lean_object* v___x_1736_; lean_object* v___x_1737_; 
v___x_1736_ = lean_apply_1(v_x_1730_, lean_box(0));
v___x_1737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1737_, 0, v___x_1736_);
return v___x_1737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___lam__0___boxed(lean_object* v_00_u03b1_1738_, lean_object* v_x_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_){
_start:
{
lean_object* v_res_1745_; 
v_res_1745_ = l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___lam__0(v_00_u03b1_1738_, v_x_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_);
lean_dec(v___y_1743_);
lean_dec_ref(v___y_1742_);
lean_dec(v___y_1741_);
lean_dec_ref(v___y_1740_);
return v_res_1745_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; 
v___x_1746_ = lean_box(0);
v___x_1747_ = lean_unsigned_to_nat(16u);
v___x_1748_ = lean_mk_array(v___x_1747_, v___x_1746_);
return v___x_1748_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; 
v___x_1749_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__0, &l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__0_once, _init_l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__0);
v___x_1750_ = lean_unsigned_to_nat(0u);
v___x_1751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1751_, 0, v___x_1750_);
lean_ctor_set(v___x_1751_, 1, v___x_1749_);
return v___x_1751_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1752_; lean_object* v___x_1753_; 
v___x_1752_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__1, &l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__1_once, _init_l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__1);
v___x_1753_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1753_, 0, lean_box(0));
lean_closure_set(v___x_1753_, 1, lean_box(0));
lean_closure_set(v___x_1753_, 2, v___x_1752_);
return v___x_1753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0(lean_object* v_input_1754_, lean_object* v_pre_1755_, lean_object* v_post_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_){
_start:
{
lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v_a_1764_; lean_object* v___x_1765_; 
v___x_1762_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__2, &l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__2_once, _init_l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__2);
v___x_1763_ = l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___lam__0(lean_box(0), v___x_1762_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_);
v_a_1764_ = lean_ctor_get(v___x_1763_, 0);
lean_inc(v_a_1764_);
lean_dec_ref(v___x_1763_);
v___x_1765_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1755_, v_post_1756_, v_input_1754_, v_a_1764_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_);
if (lean_obj_tag(v___x_1765_) == 0)
{
lean_object* v_a_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1775_; 
v_a_1766_ = lean_ctor_get(v___x_1765_, 0);
lean_inc(v_a_1766_);
lean_dec_ref_known(v___x_1765_, 1);
v___x_1767_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1767_, 0, lean_box(0));
lean_closure_set(v___x_1767_, 1, lean_box(0));
lean_closure_set(v___x_1767_, 2, v_a_1764_);
v___x_1768_ = l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___lam__0(lean_box(0), v___x_1767_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_);
v_isSharedCheck_1775_ = !lean_is_exclusive(v___x_1768_);
if (v_isSharedCheck_1775_ == 0)
{
lean_object* v_unused_1776_; 
v_unused_1776_ = lean_ctor_get(v___x_1768_, 0);
lean_dec(v_unused_1776_);
v___x_1770_ = v___x_1768_;
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
else
{
lean_dec(v___x_1768_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v___x_1773_; 
if (v_isShared_1771_ == 0)
{
lean_ctor_set(v___x_1770_, 0, v_a_1766_);
v___x_1773_ = v___x_1770_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v_a_1766_);
v___x_1773_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
return v___x_1773_;
}
}
}
else
{
lean_dec(v_a_1764_);
return v___x_1765_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___boxed(lean_object* v_input_1777_, lean_object* v_pre_1778_, lean_object* v_post_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_){
_start:
{
lean_object* v_res_1785_; 
v_res_1785_ = l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0(v_input_1777_, v_pre_1778_, v_post_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_);
lean_dec(v___y_1783_);
lean_dec_ref(v___y_1782_);
lean_dec(v___y_1781_);
lean_dec_ref(v___y_1780_);
return v_res_1785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_reduceProjs(lean_object* v_e_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_){
_start:
{
lean_object* v___f_1794_; lean_object* v___f_1795_; lean_object* v___x_1796_; 
v___f_1794_ = ((lean_object*)(l_Lean_Meta_PProdN_reduceProjs___closed__0));
v___f_1795_ = ((lean_object*)(l_Lean_Meta_PProdN_reduceProjs___closed__1));
v___x_1796_ = l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0(v_e_1788_, v___f_1794_, v___f_1795_, v_a_1789_, v_a_1790_, v_a_1791_, v_a_1792_);
return v___x_1796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_reduceProjs___boxed(lean_object* v_e_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_){
_start:
{
lean_object* v_res_1803_; 
v_res_1803_ = l_Lean_Meta_PProdN_reduceProjs(v_e_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_);
lean_dec(v_a_1801_);
lean_dec_ref(v_a_1800_);
lean_dec(v_a_1799_);
lean_dec_ref(v_a_1798_);
return v_res_1803_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_1804_, lean_object* v_m_1805_, lean_object* v_a_1806_){
_start:
{
lean_object* v___x_1807_; 
v___x_1807_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3___redArg(v_m_1805_, v_a_1806_);
return v___x_1807_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_1808_, lean_object* v_m_1809_, lean_object* v_a_1810_){
_start:
{
lean_object* v_res_1811_; 
v_res_1811_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3(v_00_u03b2_1808_, v_m_1809_, v_a_1810_);
lean_dec_ref(v_a_1810_);
lean_dec_ref(v_m_1809_);
return v_res_1811_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_1812_, lean_object* v_ref_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_){
_start:
{
lean_object* v___x_1817_; 
v___x_1817_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_1813_);
return v___x_1817_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1818_, lean_object* v_ref_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_){
_start:
{
lean_object* v_res_1823_; 
v_res_1823_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_1818_, v_ref_1819_, v___y_1820_, v___y_1821_);
lean_dec(v___y_1821_);
lean_dec_ref(v___y_1820_);
return v_res_1823_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__8(lean_object* v_00_u03b1_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_){
_start:
{
lean_object* v___x_1828_; 
v___x_1828_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__8___redArg();
return v___x_1828_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__8___boxed(lean_object* v_00_u03b1_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_){
_start:
{
lean_object* v_res_1833_; 
v_res_1833_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__8(v_00_u03b1_1829_, v___y_1830_, v___y_1831_);
lean_dec(v___y_1831_);
lean_dec_ref(v___y_1830_);
return v_res_1833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5(lean_object* v_00_u03b1_1834_, lean_object* v_x_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_){
_start:
{
lean_object* v___x_1842_; 
v___x_1842_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5___redArg(v_x_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_);
return v___x_1842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b1_1843_, lean_object* v_x_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_){
_start:
{
lean_object* v_res_1851_; 
v_res_1851_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5(v_00_u03b1_1843_, v_x_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_);
lean_dec(v___y_1849_);
lean_dec_ref(v___y_1848_);
lean_dec(v___y_1847_);
lean_dec_ref(v___y_1846_);
lean_dec(v___y_1845_);
return v_res_1851_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6(lean_object* v_00_u03b2_1852_, lean_object* v_m_1853_, lean_object* v_a_1854_, lean_object* v_b_1855_){
_start:
{
lean_object* v___x_1856_; 
v___x_1856_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6___redArg(v_m_1853_, v_a_1854_, v_b_1855_);
return v___x_1856_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b2_1857_, lean_object* v_a_1858_, lean_object* v_x_1859_){
_start:
{
lean_object* v___x_1860_; 
v___x_1860_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3_spec__4___redArg(v_a_1858_, v_x_1859_);
return v___x_1860_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3_spec__4___boxed(lean_object* v_00_u03b2_1861_, lean_object* v_a_1862_, lean_object* v_x_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3_spec__4(v_00_u03b2_1861_, v_a_1862_, v_x_1863_);
lean_dec(v_x_1863_);
lean_dec_ref(v_a_1862_);
return v_res_1864_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__10(lean_object* v_00_u03b2_1865_, lean_object* v_a_1866_, lean_object* v_x_1867_){
_start:
{
uint8_t v___x_1868_; 
v___x_1868_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__10___redArg(v_a_1866_, v_x_1867_);
return v___x_1868_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__10___boxed(lean_object* v_00_u03b2_1869_, lean_object* v_a_1870_, lean_object* v_x_1871_){
_start:
{
uint8_t v_res_1872_; lean_object* v_r_1873_; 
v_res_1872_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__10(v_00_u03b2_1869_, v_a_1870_, v_x_1871_);
lean_dec(v_x_1871_);
lean_dec_ref(v_a_1870_);
v_r_1873_ = lean_box(v_res_1872_);
return v_r_1873_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11(lean_object* v_00_u03b2_1874_, lean_object* v_data_1875_){
_start:
{
lean_object* v___x_1876_; 
v___x_1876_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11___redArg(v_data_1875_);
return v___x_1876_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__12(lean_object* v_00_u03b2_1877_, lean_object* v_a_1878_, lean_object* v_b_1879_, lean_object* v_x_1880_){
_start:
{
lean_object* v___x_1881_; 
v___x_1881_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__12___redArg(v_a_1878_, v_b_1879_, v_x_1880_);
return v___x_1881_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11_spec__12(lean_object* v_00_u03b2_1882_, lean_object* v_i_1883_, lean_object* v_source_1884_, lean_object* v_target_1885_){
_start:
{
lean_object* v___x_1886_; 
v___x_1886_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v_i_1883_, v_source_1884_, v_target_1885_);
return v___x_1886_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13(lean_object* v_00_u03b2_1887_, lean_object* v_x_1888_, lean_object* v_x_1889_){
_start:
{
lean_object* v___x_1890_; 
v___x_1890_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_x_1888_, v_x_1889_);
return v___x_1890_;
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
