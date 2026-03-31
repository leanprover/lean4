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
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
uint64_t l_Lean_ExprStructEq_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
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
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
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
static const lean_closure_object l_Lean_Meta_PProdN_genMk___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__9___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__10_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__10___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__1___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__10_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12(lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v___x_17_);
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
lean_dec_ref(v___x_85_);
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
lean_dec_ref(v___x_87_);
lean_inc(v_a_86_);
v___x_89_ = l_Lean_Meta_getLevel(v_a_86_, v_a_80_, v_a_81_, v_a_82_, v_a_83_);
if (lean_obj_tag(v___x_89_) == 0)
{
lean_object* v_a_90_; lean_object* v___x_91_; 
v_a_90_ = lean_ctor_get(v___x_89_, 0);
lean_inc(v_a_90_);
lean_dec_ref(v___x_89_);
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
lean_dec_ref(v___x_181_);
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
lean_dec_ref(v___x_260_);
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
static lean_object* _init_l_Lean_Meta_PProdN_genMk___redArg___closed__0(void){
_start:
{
lean_object* v___x_279_; 
v___x_279_ = l_instMonadEIO(lean_box(0));
return v___x_279_;
}
}
static lean_object* _init_l_Lean_Meta_PProdN_genMk___redArg___closed__1(void){
_start:
{
lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_280_ = lean_obj_once(&l_Lean_Meta_PProdN_genMk___redArg___closed__0, &l_Lean_Meta_PProdN_genMk___redArg___closed__0_once, _init_l_Lean_Meta_PProdN_genMk___redArg___closed__0);
v___x_281_ = l_StateRefT_x27_instMonad___redArg(v___x_280_);
return v___x_281_;
}
}
static lean_object* _init_l_Lean_Meta_PProdN_genMk___redArg___closed__9(void){
_start:
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_289_ = ((lean_object*)(l_Lean_Meta_PProdN_genMk___redArg___closed__8));
v___x_290_ = lean_unsigned_to_nat(2u);
v___x_291_ = lean_unsigned_to_nat(90u);
v___x_292_ = ((lean_object*)(l_Lean_Meta_PProdN_genMk___redArg___closed__7));
v___x_293_ = ((lean_object*)(l_Lean_Meta_mkPProdFst___closed__0));
v___x_294_ = l_mkPanicMessageWithDecl(v___x_293_, v___x_292_, v___x_291_, v___x_290_, v___x_289_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_genMk___redArg(lean_object* v_inst_295_, lean_object* v_mk_296_, lean_object* v_xs_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; uint8_t v___x_305_; 
v___x_303_ = lean_array_get_size(v_xs_297_);
v___x_304_ = lean_unsigned_to_nat(0u);
v___x_305_ = lean_nat_dec_eq(v___x_303_, v___x_304_);
if (v___x_305_ == 0)
{
lean_object* v___x_306_; lean_object* v_toApplicative_307_; lean_object* v_toFunctor_308_; lean_object* v_toSeq_309_; lean_object* v_toSeqLeft_310_; lean_object* v_toSeqRight_311_; lean_object* v___f_312_; lean_object* v___f_313_; lean_object* v___f_314_; lean_object* v___f_315_; lean_object* v___x_316_; lean_object* v___f_317_; lean_object* v___f_318_; lean_object* v___f_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v_toApplicative_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_361_; 
v___x_306_ = lean_obj_once(&l_Lean_Meta_PProdN_genMk___redArg___closed__1, &l_Lean_Meta_PProdN_genMk___redArg___closed__1_once, _init_l_Lean_Meta_PProdN_genMk___redArg___closed__1);
v_toApplicative_307_ = lean_ctor_get(v___x_306_, 0);
v_toFunctor_308_ = lean_ctor_get(v_toApplicative_307_, 0);
v_toSeq_309_ = lean_ctor_get(v_toApplicative_307_, 2);
v_toSeqLeft_310_ = lean_ctor_get(v_toApplicative_307_, 3);
v_toSeqRight_311_ = lean_ctor_get(v_toApplicative_307_, 4);
v___f_312_ = ((lean_object*)(l_Lean_Meta_PProdN_genMk___redArg___closed__2));
v___f_313_ = ((lean_object*)(l_Lean_Meta_PProdN_genMk___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_308_, 2);
v___f_314_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_314_, 0, v_toFunctor_308_);
v___f_315_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_315_, 0, v_toFunctor_308_);
v___x_316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_316_, 0, v___f_314_);
lean_ctor_set(v___x_316_, 1, v___f_315_);
lean_inc(v_toSeqRight_311_);
v___f_317_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_317_, 0, v_toSeqRight_311_);
lean_inc(v_toSeqLeft_310_);
v___f_318_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_318_, 0, v_toSeqLeft_310_);
lean_inc(v_toSeq_309_);
v___f_319_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_319_, 0, v_toSeq_309_);
v___x_320_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_320_, 0, v___x_316_);
lean_ctor_set(v___x_320_, 1, v___f_312_);
lean_ctor_set(v___x_320_, 2, v___f_319_);
lean_ctor_set(v___x_320_, 3, v___f_318_);
lean_ctor_set(v___x_320_, 4, v___f_317_);
v___x_321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_321_, 0, v___x_320_);
lean_ctor_set(v___x_321_, 1, v___f_313_);
v___x_322_ = l_StateRefT_x27_instMonad___redArg(v___x_321_);
v_toApplicative_323_ = lean_ctor_get(v___x_322_, 0);
v_isSharedCheck_361_ = !lean_is_exclusive(v___x_322_);
if (v_isSharedCheck_361_ == 0)
{
lean_object* v_unused_362_; 
v_unused_362_ = lean_ctor_get(v___x_322_, 1);
lean_dec(v_unused_362_);
v___x_325_ = v___x_322_;
v_isShared_326_ = v_isSharedCheck_361_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_toApplicative_323_);
lean_dec(v___x_322_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_361_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v_toFunctor_327_; lean_object* v_toSeq_328_; lean_object* v_toSeqLeft_329_; lean_object* v_toSeqRight_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_359_; 
v_toFunctor_327_ = lean_ctor_get(v_toApplicative_323_, 0);
v_toSeq_328_ = lean_ctor_get(v_toApplicative_323_, 2);
v_toSeqLeft_329_ = lean_ctor_get(v_toApplicative_323_, 3);
v_toSeqRight_330_ = lean_ctor_get(v_toApplicative_323_, 4);
v_isSharedCheck_359_ = !lean_is_exclusive(v_toApplicative_323_);
if (v_isSharedCheck_359_ == 0)
{
lean_object* v_unused_360_; 
v_unused_360_ = lean_ctor_get(v_toApplicative_323_, 1);
lean_dec(v_unused_360_);
v___x_332_ = v_toApplicative_323_;
v_isShared_333_ = v_isSharedCheck_359_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_toSeqRight_330_);
lean_inc(v_toSeqLeft_329_);
lean_inc(v_toSeq_328_);
lean_inc(v_toFunctor_327_);
lean_dec(v_toApplicative_323_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_359_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___f_334_; lean_object* v___f_335_; lean_object* v___f_336_; lean_object* v___f_337_; lean_object* v___x_338_; lean_object* v___f_339_; lean_object* v___f_340_; lean_object* v___f_341_; lean_object* v___x_343_; 
v___f_334_ = ((lean_object*)(l_Lean_Meta_PProdN_genMk___redArg___closed__4));
v___f_335_ = ((lean_object*)(l_Lean_Meta_PProdN_genMk___redArg___closed__5));
lean_inc_ref(v_toFunctor_327_);
v___f_336_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_336_, 0, v_toFunctor_327_);
v___f_337_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_337_, 0, v_toFunctor_327_);
v___x_338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_338_, 0, v___f_336_);
lean_ctor_set(v___x_338_, 1, v___f_337_);
v___f_339_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_339_, 0, v_toSeqRight_330_);
v___f_340_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_340_, 0, v_toSeqLeft_329_);
v___f_341_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_341_, 0, v_toSeq_328_);
if (v_isShared_333_ == 0)
{
lean_ctor_set(v___x_332_, 4, v___f_339_);
lean_ctor_set(v___x_332_, 3, v___f_340_);
lean_ctor_set(v___x_332_, 2, v___f_341_);
lean_ctor_set(v___x_332_, 1, v___f_334_);
lean_ctor_set(v___x_332_, 0, v___x_338_);
v___x_343_ = v___x_332_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v___x_338_);
lean_ctor_set(v_reuseFailAlloc_358_, 1, v___f_334_);
lean_ctor_set(v_reuseFailAlloc_358_, 2, v___f_341_);
lean_ctor_set(v_reuseFailAlloc_358_, 3, v___f_340_);
lean_ctor_set(v_reuseFailAlloc_358_, 4, v___f_339_);
v___x_343_ = v_reuseFailAlloc_358_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
lean_object* v___x_345_; 
if (v_isShared_326_ == 0)
{
lean_ctor_set(v___x_325_, 1, v___f_335_);
lean_ctor_set(v___x_325_, 0, v___x_343_);
v___x_345_ = v___x_325_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v___x_343_);
lean_ctor_set(v_reuseFailAlloc_357_, 1, v___f_335_);
v___x_345_ = v_reuseFailAlloc_357_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; uint8_t v___x_351_; 
v___x_346_ = lean_unsigned_to_nat(1u);
v___x_347_ = lean_nat_sub(v___x_303_, v___x_346_);
v___x_348_ = lean_array_get(v_inst_295_, v_xs_297_, v___x_347_);
lean_dec(v___x_347_);
v___x_349_ = lean_array_pop(v_xs_297_);
v___x_350_ = lean_array_get_size(v___x_349_);
v___x_351_ = lean_nat_dec_lt(v___x_304_, v___x_350_);
if (v___x_351_ == 0)
{
lean_object* v___x_352_; 
lean_dec_ref(v___x_349_);
lean_dec_ref(v___x_345_);
lean_dec_ref(v_mk_296_);
v___x_352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_352_, 0, v___x_348_);
return v___x_352_;
}
else
{
size_t v___x_353_; size_t v___x_354_; lean_object* v___x_319__overap_355_; lean_object* v___x_356_; 
v___x_353_ = lean_usize_of_nat(v___x_350_);
v___x_354_ = ((size_t)0ULL);
v___x_319__overap_355_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_345_, v_mk_296_, v___x_349_, v___x_353_, v___x_354_, v___x_348_);
lean_inc(v_a_301_);
lean_inc_ref(v_a_300_);
lean_inc(v_a_299_);
lean_inc_ref(v_a_298_);
v___x_356_ = lean_apply_5(v___x_319__overap_355_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, lean_box(0));
return v___x_356_;
}
}
}
}
}
}
else
{
lean_object* v___f_363_; lean_object* v___x_364_; lean_object* v___x_178__overap_365_; lean_object* v___x_366_; 
lean_dec_ref(v_xs_297_);
lean_dec_ref(v_mk_296_);
v___f_363_ = ((lean_object*)(l_Lean_Meta_PProdN_genMk___redArg___closed__6));
v___x_364_ = lean_obj_once(&l_Lean_Meta_PProdN_genMk___redArg___closed__9, &l_Lean_Meta_PProdN_genMk___redArg___closed__9_once, _init_l_Lean_Meta_PProdN_genMk___redArg___closed__9);
v___x_178__overap_365_ = l_panic___redArg(v___f_363_, v___x_364_);
lean_inc(v_a_301_);
lean_inc_ref(v_a_300_);
lean_inc(v_a_299_);
lean_inc_ref(v_a_298_);
v___x_366_ = lean_apply_5(v___x_178__overap_365_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, lean_box(0));
return v___x_366_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_genMk___redArg___boxed(lean_object* v_inst_367_, lean_object* v_mk_368_, lean_object* v_xs_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l_Lean_Meta_PProdN_genMk___redArg(v_inst_367_, v_mk_368_, v_xs_369_, v_a_370_, v_a_371_, v_a_372_, v_a_373_);
lean_dec(v_a_373_);
lean_dec_ref(v_a_372_);
lean_dec(v_a_371_);
lean_dec_ref(v_a_370_);
lean_dec(v_inst_367_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_genMk(lean_object* v_00_u03b1_376_, lean_object* v_inst_377_, lean_object* v_mk_378_, lean_object* v_xs_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = l_Lean_Meta_PProdN_genMk___redArg(v_inst_377_, v_mk_378_, v_xs_379_, v_a_380_, v_a_381_, v_a_382_, v_a_383_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_genMk___boxed(lean_object* v_00_u03b1_386_, lean_object* v_inst_387_, lean_object* v_mk_388_, lean_object* v_xs_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Lean_Meta_PProdN_genMk(v_00_u03b1_386_, v_inst_387_, v_mk_388_, v_xs_389_, v_a_390_, v_a_391_, v_a_392_, v_a_393_);
lean_dec(v_a_393_);
lean_dec_ref(v_a_392_);
lean_dec(v_a_391_);
lean_dec_ref(v_a_390_);
lean_dec(v_inst_387_);
return v_res_395_;
}
}
static lean_object* _init_l_Lean_Meta_PProdN_pack___closed__5(void){
_start:
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_403_ = lean_box(0);
v___x_404_ = ((lean_object*)(l_Lean_Meta_PProdN_pack___closed__4));
v___x_405_ = l_Lean_Expr_const___override(v___x_404_, v___x_403_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_pack(lean_object* v_lvl_406_, lean_object* v_xs_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_){
_start:
{
lean_object* v___x_413_; lean_object* v___x_414_; uint8_t v___x_415_; 
v___x_413_ = lean_array_get_size(v_xs_407_);
v___x_414_ = lean_unsigned_to_nat(0u);
v___x_415_ = lean_nat_dec_eq(v___x_413_, v___x_414_);
if (v___x_415_ == 0)
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
lean_dec(v_lvl_406_);
v___x_416_ = l_Lean_instInhabitedExpr;
v___x_417_ = ((lean_object*)(l_Lean_Meta_PProdN_pack___closed__0));
v___x_418_ = l_Lean_Meta_PProdN_genMk___redArg(v___x_416_, v___x_417_, v_xs_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_);
return v___x_418_;
}
else
{
uint8_t v___x_419_; 
lean_dec_ref(v_xs_407_);
v___x_419_ = l_Lean_Level_isAlwaysZero(v_lvl_406_);
if (v___x_419_ == 0)
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_420_ = ((lean_object*)(l_Lean_Meta_PProdN_pack___closed__2));
v___x_421_ = lean_box(0);
v___x_422_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_422_, 0, v_lvl_406_);
lean_ctor_set(v___x_422_, 1, v___x_421_);
v___x_423_ = l_Lean_Expr_const___override(v___x_420_, v___x_422_);
v___x_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_424_, 0, v___x_423_);
return v___x_424_;
}
else
{
lean_object* v___x_425_; lean_object* v___x_426_; 
lean_dec(v_lvl_406_);
v___x_425_ = lean_obj_once(&l_Lean_Meta_PProdN_pack___closed__5, &l_Lean_Meta_PProdN_pack___closed__5_once, _init_l_Lean_Meta_PProdN_pack___closed__5);
v___x_426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_426_, 0, v___x_425_);
return v___x_426_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_pack___boxed(lean_object* v_lvl_427_, lean_object* v_xs_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l_Lean_Meta_PProdN_pack(v_lvl_427_, v_xs_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_);
lean_dec(v_a_432_);
lean_dec_ref(v_a_431_);
lean_dec(v_a_430_);
lean_dec_ref(v_a_429_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_unpack_go___redArg(lean_object* v_e_435_, lean_object* v_remaining_436_, lean_object* v_acc_437_){
_start:
{
lean_object* v___x_442_; uint8_t v___x_443_; 
v___x_442_ = lean_unsigned_to_nat(0u);
v___x_443_ = lean_nat_dec_eq(v_remaining_436_, v___x_442_);
if (v___x_443_ == 0)
{
if (lean_obj_tag(v_e_435_) == 5)
{
lean_object* v_fn_444_; 
v_fn_444_ = lean_ctor_get(v_e_435_, 0);
if (lean_obj_tag(v_fn_444_) == 5)
{
lean_object* v_fn_445_; 
v_fn_445_ = lean_ctor_get(v_fn_444_, 0);
if (lean_obj_tag(v_fn_445_) == 4)
{
lean_object* v_declName_446_; 
v_declName_446_ = lean_ctor_get(v_fn_445_, 0);
if (lean_obj_tag(v_declName_446_) == 1)
{
lean_object* v_pre_447_; 
v_pre_447_ = lean_ctor_get(v_declName_446_, 0);
if (lean_obj_tag(v_pre_447_) == 0)
{
lean_object* v_arg_448_; lean_object* v_arg_449_; lean_object* v_str_450_; lean_object* v___x_451_; uint8_t v___x_452_; 
v_arg_448_ = lean_ctor_get(v_e_435_, 1);
v_arg_449_ = lean_ctor_get(v_fn_444_, 1);
v_str_450_ = lean_ctor_get(v_declName_446_, 1);
v___x_451_ = ((lean_object*)(l_Lean_Meta_mkPProd___closed__0));
v___x_452_ = lean_string_dec_eq(v_str_450_, v___x_451_);
if (v___x_452_ == 0)
{
lean_dec(v_remaining_436_);
goto v___jp_439_;
}
else
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
lean_inc_ref(v_arg_449_);
lean_inc_ref(v_arg_448_);
lean_dec_ref(v_e_435_);
v___x_453_ = lean_unsigned_to_nat(1u);
v___x_454_ = lean_nat_sub(v_remaining_436_, v___x_453_);
lean_dec(v_remaining_436_);
v___x_455_ = lean_array_push(v_acc_437_, v_arg_449_);
v_e_435_ = v_arg_448_;
v_remaining_436_ = v___x_454_;
v_acc_437_ = v___x_455_;
goto _start;
}
}
else
{
lean_dec(v_remaining_436_);
goto v___jp_439_;
}
}
else
{
lean_dec(v_remaining_436_);
goto v___jp_439_;
}
}
else
{
lean_dec(v_remaining_436_);
goto v___jp_439_;
}
}
else
{
lean_dec(v_remaining_436_);
goto v___jp_439_;
}
}
else
{
lean_dec(v_remaining_436_);
goto v___jp_439_;
}
}
else
{
lean_object* v___x_457_; 
lean_dec(v_remaining_436_);
lean_dec_ref(v_e_435_);
v___x_457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_457_, 0, v_acc_437_);
return v___x_457_;
}
v___jp_439_:
{
lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_440_ = lean_array_push(v_acc_437_, v_e_435_);
v___x_441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_441_, 0, v___x_440_);
return v___x_441_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_unpack_go___redArg___boxed(lean_object* v_e_458_, lean_object* v_remaining_459_, lean_object* v_acc_460_, lean_object* v_a_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_unpack_go___redArg(v_e_458_, v_remaining_459_, v_acc_460_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_unpack_go(lean_object* v_e_463_, lean_object* v_remaining_464_, lean_object* v_acc_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_unpack_go___redArg(v_e_463_, v_remaining_464_, v_acc_465_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_unpack_go___boxed(lean_object* v_e_472_, lean_object* v_remaining_473_, lean_object* v_acc_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_unpack_go(v_e_472_, v_remaining_473_, v_acc_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_);
lean_dec(v_a_478_);
lean_dec_ref(v_a_477_);
lean_dec(v_a_476_);
lean_dec_ref(v_a_475_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_unpack___redArg(lean_object* v_e_483_, lean_object* v_n_484_){
_start:
{
if (lean_obj_tag(v_e_483_) == 4)
{
lean_object* v_declName_492_; 
v_declName_492_ = lean_ctor_get(v_e_483_, 0);
if (lean_obj_tag(v_declName_492_) == 1)
{
lean_object* v_pre_493_; 
v_pre_493_ = lean_ctor_get(v_declName_492_, 0);
if (lean_obj_tag(v_pre_493_) == 0)
{
lean_object* v_str_494_; lean_object* v___x_495_; uint8_t v___x_496_; 
v_str_494_ = lean_ctor_get(v_declName_492_, 1);
v___x_495_ = ((lean_object*)(l_Lean_Meta_PProdN_pack___closed__3));
v___x_496_ = lean_string_dec_eq(v_str_494_, v___x_495_);
if (v___x_496_ == 0)
{
lean_object* v___x_497_; uint8_t v___x_498_; 
v___x_497_ = ((lean_object*)(l_Lean_Meta_PProdN_pack___closed__1));
v___x_498_ = lean_string_dec_eq(v_str_494_, v___x_497_);
if (v___x_498_ == 0)
{
goto v___jp_486_;
}
else
{
lean_dec_ref(v_e_483_);
lean_dec(v_n_484_);
goto v___jp_489_;
}
}
else
{
lean_dec_ref(v_e_483_);
lean_dec(v_n_484_);
goto v___jp_489_;
}
}
else
{
goto v___jp_486_;
}
}
else
{
goto v___jp_486_;
}
}
else
{
goto v___jp_486_;
}
v___jp_486_:
{
lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_487_ = ((lean_object*)(l_Lean_Meta_PProdN_unpack___redArg___closed__0));
v___x_488_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_unpack_go___redArg(v_e_483_, v_n_484_, v___x_487_);
return v___x_488_;
}
v___jp_489_:
{
lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_490_ = ((lean_object*)(l_Lean_Meta_PProdN_unpack___redArg___closed__0));
v___x_491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_491_, 0, v___x_490_);
return v___x_491_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_unpack___redArg___boxed(lean_object* v_e_499_, lean_object* v_n_500_, lean_object* v_a_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l_Lean_Meta_PProdN_unpack___redArg(v_e_499_, v_n_500_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_unpack(lean_object* v_e_503_, lean_object* v_n_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_){
_start:
{
lean_object* v___x_510_; 
v___x_510_ = l_Lean_Meta_PProdN_unpack___redArg(v_e_503_, v_n_504_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_unpack___boxed(lean_object* v_e_511_, lean_object* v_n_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_Lean_Meta_PProdN_unpack(v_e_511_, v_n_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_);
lean_dec(v_a_516_);
lean_dec_ref(v_a_515_);
lean_dec(v_a_514_);
lean_dec_ref(v_a_513_);
return v_res_518_;
}
}
static lean_object* _init_l_Lean_Meta_PProdN_mk___closed__4(void){
_start:
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_527_ = lean_box(0);
v___x_528_ = ((lean_object*)(l_Lean_Meta_PProdN_mk___closed__3));
v___x_529_ = l_Lean_Expr_const___override(v___x_528_, v___x_527_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_mk(lean_object* v_lvl_530_, lean_object* v_xs_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_){
_start:
{
lean_object* v___x_537_; lean_object* v___x_538_; uint8_t v___x_539_; 
v___x_537_ = lean_array_get_size(v_xs_531_);
v___x_538_ = lean_unsigned_to_nat(0u);
v___x_539_ = lean_nat_dec_eq(v___x_537_, v___x_538_);
if (v___x_539_ == 0)
{
lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
lean_dec(v_lvl_530_);
v___x_540_ = l_Lean_instInhabitedExpr;
v___x_541_ = ((lean_object*)(l_Lean_Meta_PProdN_mk___closed__0));
v___x_542_ = l_Lean_Meta_PProdN_genMk___redArg(v___x_540_, v___x_541_, v_xs_531_, v_a_532_, v_a_533_, v_a_534_, v_a_535_);
return v___x_542_;
}
else
{
uint8_t v___x_543_; 
lean_dec_ref(v_xs_531_);
v___x_543_ = l_Lean_Level_isAlwaysZero(v_lvl_530_);
if (v___x_543_ == 0)
{
lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_544_ = ((lean_object*)(l_Lean_Meta_PProdN_mk___closed__2));
v___x_545_ = lean_box(0);
v___x_546_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_546_, 0, v_lvl_530_);
lean_ctor_set(v___x_546_, 1, v___x_545_);
v___x_547_ = l_Lean_Expr_const___override(v___x_544_, v___x_546_);
v___x_548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_548_, 0, v___x_547_);
return v___x_548_;
}
else
{
lean_object* v___x_549_; lean_object* v___x_550_; 
lean_dec(v_lvl_530_);
v___x_549_ = lean_obj_once(&l_Lean_Meta_PProdN_mk___closed__4, &l_Lean_Meta_PProdN_mk___closed__4_once, _init_l_Lean_Meta_PProdN_mk___closed__4);
v___x_550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_550_, 0, v___x_549_);
return v___x_550_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_mk___boxed(lean_object* v_lvl_551_, lean_object* v_xs_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l_Lean_Meta_PProdN_mk(v_lvl_551_, v_xs_552_, v_a_553_, v_a_554_, v_a_555_, v_a_556_);
lean_dec(v_a_556_);
lean_dec_ref(v_a_555_);
lean_dec(v_a_554_);
lean_dec_ref(v_a_553_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_proj_spec__0___redArg(lean_object* v_upperBound_559_, lean_object* v_a_560_, lean_object* v_b_561_){
_start:
{
uint8_t v___x_562_; 
v___x_562_ = lean_nat_dec_lt(v_a_560_, v_upperBound_559_);
if (v___x_562_ == 0)
{
lean_dec(v_a_560_);
return v_b_561_;
}
else
{
lean_object* v_fst_563_; lean_object* v_snd_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_576_; 
v_fst_563_ = lean_ctor_get(v_b_561_, 0);
v_snd_564_ = lean_ctor_get(v_b_561_, 1);
v_isSharedCheck_576_ = !lean_is_exclusive(v_b_561_);
if (v_isSharedCheck_576_ == 0)
{
v___x_566_ = v_b_561_;
v_isShared_567_ = v_isSharedCheck_576_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_snd_564_);
lean_inc(v_fst_563_);
lean_dec(v_b_561_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_576_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_571_; 
lean_inc(v_fst_563_);
v___x_568_ = l_Lean_Meta_mkPProdSnd(v_fst_563_, v_snd_564_);
v___x_569_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_mkTypeSnd(v_fst_563_);
if (v_isShared_567_ == 0)
{
lean_ctor_set(v___x_566_, 1, v___x_568_);
lean_ctor_set(v___x_566_, 0, v___x_569_);
v___x_571_ = v___x_566_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v___x_569_);
lean_ctor_set(v_reuseFailAlloc_575_, 1, v___x_568_);
v___x_571_ = v_reuseFailAlloc_575_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_572_ = lean_unsigned_to_nat(1u);
v___x_573_ = lean_nat_add(v_a_560_, v___x_572_);
lean_dec(v_a_560_);
v_a_560_ = v___x_573_;
v_b_561_ = v___x_571_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_proj_spec__0___redArg___boxed(lean_object* v_upperBound_577_, lean_object* v_a_578_, lean_object* v_b_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_proj_spec__0___redArg(v_upperBound_577_, v_a_578_, v_b_579_);
lean_dec(v_upperBound_577_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_proj(lean_object* v_n_581_, lean_object* v_i_582_, lean_object* v_t_583_, lean_object* v_e_584_){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v_fst_588_; lean_object* v_snd_589_; lean_object* v___x_590_; lean_object* v___x_591_; uint8_t v___x_592_; 
v___x_585_ = lean_unsigned_to_nat(0u);
v___x_586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_586_, 0, v_t_583_);
lean_ctor_set(v___x_586_, 1, v_e_584_);
v___x_587_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_proj_spec__0___redArg(v_i_582_, v___x_585_, v___x_586_);
v_fst_588_ = lean_ctor_get(v___x_587_, 0);
lean_inc(v_fst_588_);
v_snd_589_ = lean_ctor_get(v___x_587_, 1);
lean_inc(v_snd_589_);
lean_dec_ref(v___x_587_);
v___x_590_ = lean_unsigned_to_nat(1u);
v___x_591_ = lean_nat_add(v_i_582_, v___x_590_);
v___x_592_ = lean_nat_dec_lt(v___x_591_, v_n_581_);
lean_dec(v___x_591_);
if (v___x_592_ == 0)
{
lean_dec(v_fst_588_);
return v_snd_589_;
}
else
{
lean_object* v___x_593_; 
v___x_593_ = l_Lean_Meta_mkPProdFst(v_fst_588_, v_snd_589_);
return v___x_593_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_proj___boxed(lean_object* v_n_594_, lean_object* v_i_595_, lean_object* v_t_596_, lean_object* v_e_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l_Lean_Meta_PProdN_proj(v_n_594_, v_i_595_, v_t_596_, v_e_597_);
lean_dec(v_i_595_);
lean_dec(v_n_594_);
return v_res_598_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_proj_spec__0(lean_object* v_upperBound_599_, lean_object* v_inst_600_, lean_object* v_R_601_, lean_object* v_a_602_, lean_object* v_b_603_, lean_object* v_c_604_){
_start:
{
lean_object* v___x_605_; 
v___x_605_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_proj_spec__0___redArg(v_upperBound_599_, v_a_602_, v_b_603_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_proj_spec__0___boxed(lean_object* v_upperBound_606_, lean_object* v_inst_607_, lean_object* v_R_608_, lean_object* v_a_609_, lean_object* v_b_610_, lean_object* v_c_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_proj_spec__0(v_upperBound_606_, v_inst_607_, v_R_608_, v_a_609_, v_b_610_, v_c_611_);
lean_dec(v_upperBound_606_);
return v_res_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_projs___lam__0(lean_object* v_n_613_, lean_object* v_t_614_, lean_object* v_e_615_, lean_object* v_i_616_){
_start:
{
lean_object* v___x_617_; 
v___x_617_ = l_Lean_Meta_PProdN_proj(v_n_613_, v_i_616_, v_t_614_, v_e_615_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_projs___lam__0___boxed(lean_object* v_n_618_, lean_object* v_t_619_, lean_object* v_e_620_, lean_object* v_i_621_){
_start:
{
lean_object* v_res_622_; 
v_res_622_ = l_Lean_Meta_PProdN_projs___lam__0(v_n_618_, v_t_619_, v_e_620_, v_i_621_);
lean_dec(v_i_621_);
lean_dec(v_n_618_);
return v_res_622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_projs(lean_object* v_n_623_, lean_object* v_t_624_, lean_object* v_e_625_){
_start:
{
lean_object* v___f_626_; lean_object* v___x_627_; 
lean_inc(v_n_623_);
v___f_626_ = lean_alloc_closure((void*)(l_Lean_Meta_PProdN_projs___lam__0___boxed), 4, 3);
lean_closure_set(v___f_626_, 0, v_n_623_);
lean_closure_set(v___f_626_, 1, v_t_624_);
lean_closure_set(v___f_626_, 2, v_e_625_);
v___x_627_ = l_Array_ofFn___redArg(v_n_623_, v___f_626_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_projM_spec__0___redArg(lean_object* v_upperBound_628_, lean_object* v_a_629_, lean_object* v_b_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_){
_start:
{
uint8_t v___x_636_; 
v___x_636_ = lean_nat_dec_lt(v_a_629_, v_upperBound_628_);
if (v___x_636_ == 0)
{
lean_object* v___x_637_; 
lean_dec(v_a_629_);
v___x_637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_637_, 0, v_b_630_);
return v___x_637_;
}
else
{
lean_object* v___x_638_; 
v___x_638_ = l_Lean_Meta_mkPProdSndM(v_b_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_);
if (lean_obj_tag(v___x_638_) == 0)
{
lean_object* v_a_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
v_a_639_ = lean_ctor_get(v___x_638_, 0);
lean_inc(v_a_639_);
lean_dec_ref(v___x_638_);
v___x_640_ = lean_unsigned_to_nat(1u);
v___x_641_ = lean_nat_add(v_a_629_, v___x_640_);
lean_dec(v_a_629_);
v_a_629_ = v___x_641_;
v_b_630_ = v_a_639_;
goto _start;
}
else
{
lean_dec(v_a_629_);
return v___x_638_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_projM_spec__0___redArg___boxed(lean_object* v_upperBound_643_, lean_object* v_a_644_, lean_object* v_b_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_projM_spec__0___redArg(v_upperBound_643_, v_a_644_, v_b_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_);
lean_dec(v___y_649_);
lean_dec_ref(v___y_648_);
lean_dec(v___y_647_);
lean_dec_ref(v___y_646_);
lean_dec(v_upperBound_643_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_projM(lean_object* v_n_652_, lean_object* v_i_653_, lean_object* v_e_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_){
_start:
{
lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_660_ = lean_unsigned_to_nat(0u);
v___x_661_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_projM_spec__0___redArg(v_i_653_, v___x_660_, v_e_654_, v_a_655_, v_a_656_, v_a_657_, v_a_658_);
if (lean_obj_tag(v___x_661_) == 0)
{
lean_object* v_a_662_; lean_object* v___x_663_; lean_object* v___x_664_; uint8_t v___x_665_; 
v_a_662_ = lean_ctor_get(v___x_661_, 0);
lean_inc(v_a_662_);
v___x_663_ = lean_unsigned_to_nat(1u);
v___x_664_ = lean_nat_add(v_i_653_, v___x_663_);
v___x_665_ = lean_nat_dec_lt(v___x_664_, v_n_652_);
lean_dec(v___x_664_);
if (v___x_665_ == 0)
{
lean_dec(v_a_662_);
return v___x_661_;
}
else
{
lean_object* v___x_666_; 
lean_dec_ref(v___x_661_);
v___x_666_ = l_Lean_Meta_mkPProdFstM(v_a_662_, v_a_655_, v_a_656_, v_a_657_, v_a_658_);
return v___x_666_;
}
}
else
{
return v___x_661_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_projM___boxed(lean_object* v_n_667_, lean_object* v_i_668_, lean_object* v_e_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l_Lean_Meta_PProdN_projM(v_n_667_, v_i_668_, v_e_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_);
lean_dec(v_a_673_);
lean_dec_ref(v_a_672_);
lean_dec(v_a_671_);
lean_dec_ref(v_a_670_);
lean_dec(v_i_668_);
lean_dec(v_n_667_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_projM_spec__0(lean_object* v_upperBound_676_, lean_object* v_inst_677_, lean_object* v_R_678_, lean_object* v_a_679_, lean_object* v_b_680_, lean_object* v_c_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_){
_start:
{
lean_object* v___x_687_; 
v___x_687_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_projM_spec__0___redArg(v_upperBound_676_, v_a_679_, v_b_680_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_projM_spec__0___boxed(lean_object* v_upperBound_688_, lean_object* v_inst_689_, lean_object* v_R_690_, lean_object* v_a_691_, lean_object* v_b_692_, lean_object* v_c_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_projM_spec__0(v_upperBound_688_, v_inst_689_, v_R_690_, v_a_691_, v_b_692_, v_c_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_);
lean_dec(v___y_697_);
lean_dec_ref(v___y_696_);
lean_dec(v___y_695_);
lean_dec_ref(v___y_694_);
lean_dec(v_upperBound_688_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_PProdN_packLambdas_spec__0(lean_object* v_msg_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_){
_start:
{
lean_object* v___f_706_; lean_object* v___x_407__overap_707_; lean_object* v___x_708_; 
v___f_706_ = ((lean_object*)(l_Lean_Meta_PProdN_genMk___redArg___closed__6));
v___x_407__overap_707_ = lean_panic_fn_borrowed(v___f_706_, v_msg_700_);
lean_inc(v___y_704_);
lean_inc_ref(v___y_703_);
lean_inc(v___y_702_);
lean_inc_ref(v___y_701_);
v___x_708_ = lean_apply_5(v___x_407__overap_707_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, lean_box(0));
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_PProdN_packLambdas_spec__0___boxed(lean_object* v_msg_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_){
_start:
{
lean_object* v_res_715_; 
v_res_715_ = l_panic___at___00Lean_Meta_PProdN_packLambdas_spec__0(v_msg_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_);
lean_dec(v___y_713_);
lean_dec_ref(v___y_712_);
lean_dec(v___y_711_);
lean_dec_ref(v___y_710_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___redArg___lam__0(lean_object* v_k_716_, lean_object* v_b_717_, lean_object* v_c_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_){
_start:
{
lean_object* v___x_724_; 
lean_inc(v___y_722_);
lean_inc_ref(v___y_721_);
lean_inc(v___y_720_);
lean_inc_ref(v___y_719_);
v___x_724_ = lean_apply_7(v_k_716_, v_b_717_, v_c_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, lean_box(0));
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___redArg___lam__0___boxed(lean_object* v_k_725_, lean_object* v_b_726_, lean_object* v_c_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_){
_start:
{
lean_object* v_res_733_; 
v_res_733_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___redArg___lam__0(v_k_725_, v_b_726_, v_c_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_);
lean_dec(v___y_731_);
lean_dec_ref(v___y_730_);
lean_dec(v___y_729_);
lean_dec_ref(v___y_728_);
return v_res_733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___redArg(lean_object* v_type_734_, lean_object* v_k_735_, uint8_t v_cleanupAnnotations_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_){
_start:
{
lean_object* v___f_742_; uint8_t v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
v___f_742_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_742_, 0, v_k_735_);
v___x_743_ = 0;
v___x_744_ = lean_box(0);
v___x_745_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_743_, v___x_744_, v_type_734_, v___f_742_, v_cleanupAnnotations_736_, v___x_743_, v___y_737_, v___y_738_, v___y_739_, v___y_740_);
if (lean_obj_tag(v___x_745_) == 0)
{
lean_object* v_a_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_753_; 
v_a_746_ = lean_ctor_get(v___x_745_, 0);
v_isSharedCheck_753_ = !lean_is_exclusive(v___x_745_);
if (v_isSharedCheck_753_ == 0)
{
v___x_748_ = v___x_745_;
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_a_746_);
lean_dec(v___x_745_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_751_; 
if (v_isShared_749_ == 0)
{
v___x_751_ = v___x_748_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v_a_746_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
return v___x_751_;
}
}
}
else
{
lean_object* v_a_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_761_; 
v_a_754_ = lean_ctor_get(v___x_745_, 0);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_745_);
if (v_isSharedCheck_761_ == 0)
{
v___x_756_ = v___x_745_;
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_a_754_);
lean_dec(v___x_745_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_759_; 
if (v_isShared_757_ == 0)
{
v___x_759_ = v___x_756_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_a_754_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___redArg___boxed(lean_object* v_type_762_, lean_object* v_k_763_, lean_object* v_cleanupAnnotations_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_770_; lean_object* v_res_771_; 
v_cleanupAnnotations_boxed_770_ = lean_unbox(v_cleanupAnnotations_764_);
v_res_771_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___redArg(v_type_762_, v_k_763_, v_cleanupAnnotations_boxed_770_, v___y_765_, v___y_766_, v___y_767_, v___y_768_);
lean_dec(v___y_768_);
lean_dec_ref(v___y_767_);
lean_dec(v___y_766_);
lean_dec_ref(v___y_765_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2(lean_object* v_00_u03b1_772_, lean_object* v_type_773_, lean_object* v_k_774_, uint8_t v_cleanupAnnotations_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_){
_start:
{
lean_object* v___x_781_; 
v___x_781_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___redArg(v_type_773_, v_k_774_, v_cleanupAnnotations_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___boxed(lean_object* v_00_u03b1_782_, lean_object* v_type_783_, lean_object* v_k_784_, lean_object* v_cleanupAnnotations_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_791_; lean_object* v_res_792_; 
v_cleanupAnnotations_boxed_791_ = lean_unbox(v_cleanupAnnotations_785_);
v_res_792_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2(v_00_u03b1_782_, v_type_783_, v_k_784_, v_cleanupAnnotations_boxed_791_, v___y_786_, v___y_787_, v___y_788_, v___y_789_);
lean_dec(v___y_789_);
lean_dec_ref(v___y_788_);
lean_dec(v___y_787_);
lean_dec_ref(v___y_786_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_PProdN_packLambdas_spec__1(lean_object* v_xs_793_, size_t v_sz_794_, size_t v_i_795_, lean_object* v_bs_796_){
_start:
{
uint8_t v___x_797_; 
v___x_797_ = lean_usize_dec_lt(v_i_795_, v_sz_794_);
if (v___x_797_ == 0)
{
lean_dec_ref(v_xs_793_);
return v_bs_796_;
}
else
{
lean_object* v_v_798_; lean_object* v___x_799_; lean_object* v_bs_x27_800_; lean_object* v___x_801_; size_t v___x_802_; size_t v___x_803_; lean_object* v___x_804_; 
v_v_798_ = lean_array_uget(v_bs_796_, v_i_795_);
v___x_799_ = lean_unsigned_to_nat(0u);
v_bs_x27_800_ = lean_array_uset(v_bs_796_, v_i_795_, v___x_799_);
lean_inc_ref(v_xs_793_);
v___x_801_ = l_Lean_Expr_beta(v_v_798_, v_xs_793_);
v___x_802_ = ((size_t)1ULL);
v___x_803_ = lean_usize_add(v_i_795_, v___x_802_);
v___x_804_ = lean_array_uset(v_bs_x27_800_, v_i_795_, v___x_801_);
v_i_795_ = v___x_803_;
v_bs_796_ = v___x_804_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_PProdN_packLambdas_spec__1___boxed(lean_object* v_xs_806_, lean_object* v_sz_807_, lean_object* v_i_808_, lean_object* v_bs_809_){
_start:
{
size_t v_sz_boxed_810_; size_t v_i_boxed_811_; lean_object* v_res_812_; 
v_sz_boxed_810_ = lean_unbox_usize(v_sz_807_);
lean_dec(v_sz_807_);
v_i_boxed_811_ = lean_unbox_usize(v_i_808_);
lean_dec(v_i_808_);
v_res_812_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_PProdN_packLambdas_spec__1(v_xs_806_, v_sz_boxed_810_, v_i_boxed_811_, v_bs_809_);
return v_res_812_;
}
}
static lean_object* _init_l_Lean_Meta_PProdN_packLambdas___lam__0___closed__2(void){
_start:
{
lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_815_ = ((lean_object*)(l_Lean_Meta_PProdN_packLambdas___lam__0___closed__1));
v___x_816_ = lean_unsigned_to_nat(4u);
v___x_817_ = lean_unsigned_to_nat(175u);
v___x_818_ = ((lean_object*)(l_Lean_Meta_PProdN_packLambdas___lam__0___closed__0));
v___x_819_ = ((lean_object*)(l_Lean_Meta_mkPProdFst___closed__0));
v___x_820_ = l_mkPanicMessageWithDecl(v___x_819_, v___x_818_, v___x_817_, v___x_816_, v___x_815_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_packLambdas___lam__0(lean_object* v_es_821_, uint8_t v___x_822_, lean_object* v_xs_823_, lean_object* v_sort_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_){
_start:
{
uint8_t v___x_830_; 
v___x_830_ = l_Lean_Expr_isSort(v_sort_824_);
if (v___x_830_ == 0)
{
lean_object* v___x_831_; lean_object* v___x_832_; 
lean_dec_ref(v_xs_823_);
lean_dec_ref(v_es_821_);
v___x_831_ = lean_obj_once(&l_Lean_Meta_PProdN_packLambdas___lam__0___closed__2, &l_Lean_Meta_PProdN_packLambdas___lam__0___closed__2_once, _init_l_Lean_Meta_PProdN_packLambdas___lam__0___closed__2);
v___x_832_ = l_panic___at___00Lean_Meta_PProdN_packLambdas_spec__0(v___x_831_, v___y_825_, v___y_826_, v___y_827_, v___y_828_);
return v___x_832_;
}
else
{
size_t v_sz_833_; size_t v___x_834_; lean_object* v_es_x27_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
v_sz_833_ = lean_array_size(v_es_821_);
v___x_834_ = ((size_t)0ULL);
lean_inc_ref(v_xs_823_);
v_es_x27_835_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_PProdN_packLambdas_spec__1(v_xs_823_, v_sz_833_, v___x_834_, v_es_821_);
v___x_836_ = l_Lean_Expr_sortLevel_x21(v_sort_824_);
v___x_837_ = l_Lean_Meta_PProdN_pack(v___x_836_, v_es_x27_835_, v___y_825_, v___y_826_, v___y_827_, v___y_828_);
if (lean_obj_tag(v___x_837_) == 0)
{
lean_object* v_a_838_; uint8_t v___x_839_; lean_object* v___x_840_; 
v_a_838_ = lean_ctor_get(v___x_837_, 0);
lean_inc(v_a_838_);
lean_dec_ref(v___x_837_);
v___x_839_ = 1;
v___x_840_ = l_Lean_Meta_mkLambdaFVars(v_xs_823_, v_a_838_, v___x_822_, v___x_830_, v___x_822_, v___x_830_, v___x_839_, v___y_825_, v___y_826_, v___y_827_, v___y_828_);
lean_dec_ref(v_xs_823_);
return v___x_840_;
}
else
{
lean_dec_ref(v_xs_823_);
return v___x_837_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_packLambdas___lam__0___boxed(lean_object* v_es_841_, lean_object* v___x_842_, lean_object* v_xs_843_, lean_object* v_sort_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_){
_start:
{
uint8_t v___x_1006__boxed_850_; lean_object* v_res_851_; 
v___x_1006__boxed_850_ = lean_unbox(v___x_842_);
v_res_851_ = l_Lean_Meta_PProdN_packLambdas___lam__0(v_es_841_, v___x_1006__boxed_850_, v_xs_843_, v_sort_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec_ref(v_sort_844_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_packLambdas(lean_object* v_type_852_, lean_object* v_es_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_){
_start:
{
lean_object* v___x_859_; lean_object* v___x_860_; uint8_t v___x_861_; 
v___x_859_ = lean_array_get_size(v_es_853_);
v___x_860_ = lean_unsigned_to_nat(1u);
v___x_861_ = lean_nat_dec_eq(v___x_859_, v___x_860_);
if (v___x_861_ == 0)
{
lean_object* v___x_862_; lean_object* v___f_863_; lean_object* v___x_864_; 
v___x_862_ = lean_box(v___x_861_);
v___f_863_ = lean_alloc_closure((void*)(l_Lean_Meta_PProdN_packLambdas___lam__0___boxed), 9, 2);
lean_closure_set(v___f_863_, 0, v_es_853_);
lean_closure_set(v___f_863_, 1, v___x_862_);
v___x_864_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___redArg(v_type_852_, v___f_863_, v___x_861_, v_a_854_, v_a_855_, v_a_856_, v_a_857_);
return v___x_864_;
}
else
{
lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; 
lean_dec_ref(v_type_852_);
v___x_865_ = lean_unsigned_to_nat(0u);
v___x_866_ = lean_array_fget(v_es_853_, v___x_865_);
lean_dec_ref(v_es_853_);
v___x_867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_867_, 0, v___x_866_);
return v___x_867_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_packLambdas___boxed(lean_object* v_type_868_, lean_object* v_es_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_){
_start:
{
lean_object* v_res_875_; 
v_res_875_ = l_Lean_Meta_PProdN_packLambdas(v_type_868_, v_es_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_);
lean_dec(v_a_873_);
lean_dec_ref(v_a_872_);
lean_dec(v_a_871_);
lean_dec_ref(v_a_870_);
return v_res_875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_mkLambdas___lam__0(lean_object* v_es_876_, uint8_t v___x_877_, lean_object* v_xs_878_, lean_object* v_body_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_){
_start:
{
lean_object* v___x_885_; 
v___x_885_ = l_Lean_Meta_getLevel(v_body_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_);
if (lean_obj_tag(v___x_885_) == 0)
{
lean_object* v_a_886_; size_t v_sz_887_; size_t v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
v_a_886_ = lean_ctor_get(v___x_885_, 0);
lean_inc(v_a_886_);
lean_dec_ref(v___x_885_);
v_sz_887_ = lean_array_size(v_es_876_);
v___x_888_ = ((size_t)0ULL);
lean_inc_ref(v_xs_878_);
v___x_889_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_PProdN_packLambdas_spec__1(v_xs_878_, v_sz_887_, v___x_888_, v_es_876_);
v___x_890_ = l_Lean_Meta_PProdN_mk(v_a_886_, v___x_889_, v___y_880_, v___y_881_, v___y_882_, v___y_883_);
if (lean_obj_tag(v___x_890_) == 0)
{
lean_object* v_a_891_; uint8_t v___x_892_; uint8_t v___x_893_; lean_object* v___x_894_; 
v_a_891_ = lean_ctor_get(v___x_890_, 0);
lean_inc(v_a_891_);
lean_dec_ref(v___x_890_);
v___x_892_ = 1;
v___x_893_ = 1;
v___x_894_ = l_Lean_Meta_mkLambdaFVars(v_xs_878_, v_a_891_, v___x_877_, v___x_892_, v___x_877_, v___x_892_, v___x_893_, v___y_880_, v___y_881_, v___y_882_, v___y_883_);
lean_dec_ref(v_xs_878_);
return v___x_894_;
}
else
{
lean_dec_ref(v_xs_878_);
return v___x_890_;
}
}
else
{
lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_902_; 
lean_dec_ref(v_xs_878_);
lean_dec_ref(v_es_876_);
v_a_895_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_902_ == 0)
{
v___x_897_ = v___x_885_;
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_dec(v___x_885_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_mkLambdas___lam__0___boxed(lean_object* v_es_903_, lean_object* v___x_904_, lean_object* v_xs_905_, lean_object* v_body_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_){
_start:
{
uint8_t v___x_371__boxed_912_; lean_object* v_res_913_; 
v___x_371__boxed_912_ = lean_unbox(v___x_904_);
v_res_913_ = l_Lean_Meta_PProdN_mkLambdas___lam__0(v_es_903_, v___x_371__boxed_912_, v_xs_905_, v_body_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_);
lean_dec(v___y_910_);
lean_dec_ref(v___y_909_);
lean_dec(v___y_908_);
lean_dec_ref(v___y_907_);
return v_res_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_mkLambdas(lean_object* v_type_914_, lean_object* v_es_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_){
_start:
{
lean_object* v___x_921_; lean_object* v___x_922_; uint8_t v___x_923_; 
v___x_921_ = lean_array_get_size(v_es_915_);
v___x_922_ = lean_unsigned_to_nat(1u);
v___x_923_ = lean_nat_dec_eq(v___x_921_, v___x_922_);
if (v___x_923_ == 0)
{
lean_object* v___x_924_; lean_object* v___f_925_; lean_object* v___x_926_; 
v___x_924_ = lean_box(v___x_923_);
v___f_925_ = lean_alloc_closure((void*)(l_Lean_Meta_PProdN_mkLambdas___lam__0___boxed), 9, 2);
lean_closure_set(v___f_925_, 0, v_es_915_);
lean_closure_set(v___f_925_, 1, v___x_924_);
v___x_926_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___redArg(v_type_914_, v___f_925_, v___x_923_, v_a_916_, v_a_917_, v_a_918_, v_a_919_);
return v___x_926_;
}
else
{
lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
lean_dec_ref(v_type_914_);
v___x_927_ = lean_unsigned_to_nat(0u);
v___x_928_ = lean_array_fget(v_es_915_, v___x_927_);
lean_dec_ref(v_es_915_);
v___x_929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_929_, 0, v___x_928_);
return v___x_929_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_mkLambdas___boxed(lean_object* v_type_930_, lean_object* v_es_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l_Lean_Meta_PProdN_mkLambdas(v_type_930_, v_es_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_);
lean_dec(v_a_935_);
lean_dec_ref(v_a_934_);
lean_dec(v_a_933_);
lean_dec_ref(v_a_932_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_stripProjs(lean_object* v_e_938_){
_start:
{
if (lean_obj_tag(v_e_938_) == 11)
{
lean_object* v_typeName_939_; 
v_typeName_939_ = lean_ctor_get(v_e_938_, 0);
if (lean_obj_tag(v_typeName_939_) == 1)
{
lean_object* v_pre_940_; 
v_pre_940_ = lean_ctor_get(v_typeName_939_, 0);
if (lean_obj_tag(v_pre_940_) == 0)
{
lean_object* v_struct_941_; lean_object* v_str_942_; lean_object* v___x_943_; uint8_t v___x_944_; 
v_struct_941_ = lean_ctor_get(v_e_938_, 2);
v_str_942_ = lean_ctor_get(v_typeName_939_, 1);
v___x_943_ = ((lean_object*)(l_Lean_Meta_mkPProd___closed__0));
v___x_944_ = lean_string_dec_eq(v_str_942_, v___x_943_);
if (v___x_944_ == 0)
{
lean_object* v___x_945_; uint8_t v___x_946_; 
v___x_945_ = ((lean_object*)(l_Lean_Meta_mkPProd___closed__2));
v___x_946_ = lean_string_dec_eq(v_str_942_, v___x_945_);
if (v___x_946_ == 0)
{
lean_inc_ref(v_e_938_);
return v_e_938_;
}
else
{
v_e_938_ = v_struct_941_;
goto _start;
}
}
else
{
v_e_938_ = v_struct_941_;
goto _start;
}
}
else
{
lean_inc_ref(v_e_938_);
return v_e_938_;
}
}
else
{
lean_inc_ref(v_e_938_);
return v_e_938_;
}
}
else
{
lean_inc_ref(v_e_938_);
return v_e_938_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_stripProjs___boxed(lean_object* v_e_949_){
_start:
{
lean_object* v_res_950_; 
v_res_950_ = l_Lean_Meta_PProdN_stripProjs(v_e_949_);
lean_dec_ref(v_e_949_);
return v_res_950_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___redArg(lean_object* v_e_953_, lean_object* v_i_954_){
_start:
{
uint8_t v___y_957_; lean_object* v___x_971_; lean_object* v___x_972_; uint8_t v___x_973_; 
v___x_971_ = ((lean_object*)(l_Lean_Meta_mkPProdMk___closed__1));
v___x_972_ = lean_unsigned_to_nat(4u);
v___x_973_ = l_Lean_Expr_isAppOfArity(v_e_953_, v___x_971_, v___x_972_);
if (v___x_973_ == 0)
{
lean_object* v___x_974_; lean_object* v___x_975_; uint8_t v___x_976_; 
v___x_974_ = ((lean_object*)(l_Lean_Meta_mkPProdMk___closed__3));
v___x_975_ = lean_unsigned_to_nat(2u);
v___x_976_ = l_Lean_Expr_isAppOfArity(v_e_953_, v___x_974_, v___x_975_);
v___y_957_ = v___x_976_;
goto v___jp_956_;
}
else
{
v___y_957_ = v___x_973_;
goto v___jp_956_;
}
v___jp_956_:
{
if (v___y_957_ == 0)
{
lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_958_ = ((lean_object*)(l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___redArg___closed__0));
v___x_959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_959_, 0, v___x_958_);
return v___x_959_;
}
else
{
lean_object* v___x_960_; uint8_t v___x_961_; 
v___x_960_ = lean_unsigned_to_nat(0u);
v___x_961_ = lean_nat_dec_eq(v_i_954_, v___x_960_);
if (v___x_961_ == 0)
{
lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_962_ = l_Lean_Expr_appArg_x21(v_e_953_);
v___x_963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_963_, 0, v___x_962_);
v___x_964_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_964_, 0, v___x_963_);
v___x_965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_965_, 0, v___x_964_);
return v___x_965_;
}
else
{
lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_966_ = l_Lean_Expr_appFn_x21(v_e_953_);
v___x_967_ = l_Lean_Expr_appArg_x21(v___x_966_);
lean_dec_ref(v___x_966_);
v___x_968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_968_, 0, v___x_967_);
v___x_969_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_969_, 0, v___x_968_);
v___x_970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_970_, 0, v___x_969_);
return v___x_970_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___redArg___boxed(lean_object* v_e_977_, lean_object* v_i_978_, lean_object* v_a_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___redArg(v_e_977_, v_i_978_);
lean_dec(v_i_978_);
lean_dec_ref(v_e_977_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce(lean_object* v_e_981_, lean_object* v_i_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_){
_start:
{
lean_object* v___x_988_; 
v___x_988_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___redArg(v_e_981_, v_i_982_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___boxed(lean_object* v_e_989_, lean_object* v_i_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_){
_start:
{
lean_object* v_res_996_; 
v_res_996_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce(v_e_989_, v_i_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_);
lean_dec(v_a_994_);
lean_dec_ref(v_a_993_);
lean_dec(v_a_992_);
lean_dec_ref(v_a_991_);
lean_dec(v_i_990_);
lean_dec_ref(v_e_989_);
return v_res_996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_reduceProjs___lam__0(lean_object* v_x_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_){
_start:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1003_ = ((lean_object*)(l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___redArg___closed__0));
v___x_1004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1004_, 0, v___x_1003_);
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_reduceProjs___lam__0___boxed(lean_object* v_x_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_){
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l_Lean_Meta_PProdN_reduceProjs___lam__0(v_x_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_);
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
lean_dec_ref(v_x_1005_);
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_reduceProjs___lam__1(lean_object* v_e_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_){
_start:
{
lean_object* v_e_x27_1035_; lean_object* v_e_x27_1039_; lean_object* v___x_1042_; 
lean_inc_ref(v_e_1028_);
v___x_1042_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1028_, v___y_1030_);
if (lean_obj_tag(v___x_1042_) == 0)
{
lean_object* v_a_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1072_; 
v_a_1043_ = lean_ctor_get(v___x_1042_, 0);
v_isSharedCheck_1072_ = !lean_is_exclusive(v___x_1042_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1045_ = v___x_1042_;
v_isShared_1046_ = v_isSharedCheck_1072_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_a_1043_);
lean_dec(v___x_1042_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1072_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v___x_1056_; uint8_t v___x_1057_; 
v___x_1056_ = l_Lean_Expr_cleanupAnnotations(v_a_1043_);
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
lean_del_object(v___x_1045_);
lean_dec_ref(v_e_1028_);
v_e_x27_1035_ = v_arg_1058_;
goto v___jp_1034_;
}
}
else
{
lean_dec_ref(v___x_1063_);
lean_del_object(v___x_1045_);
lean_dec_ref(v_e_1028_);
v_e_x27_1035_ = v_arg_1058_;
goto v___jp_1034_;
}
}
else
{
lean_dec_ref(v___x_1063_);
lean_del_object(v___x_1045_);
lean_dec_ref(v_e_1028_);
v_e_x27_1039_ = v_arg_1058_;
goto v___jp_1038_;
}
}
else
{
lean_dec_ref(v___x_1063_);
lean_del_object(v___x_1045_);
lean_dec_ref(v_e_1028_);
v_e_x27_1039_ = v_arg_1058_;
goto v___jp_1038_;
}
}
}
}
v___jp_1047_:
{
uint8_t v___x_1048_; 
v___x_1048_ = l_Lean_Expr_isProj(v_e_1028_);
if (v___x_1048_ == 0)
{
lean_object* v___x_1049_; lean_object* v___x_1051_; 
lean_dec_ref(v_e_1028_);
v___x_1049_ = ((lean_object*)(l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___redArg___closed__0));
if (v_isShared_1046_ == 0)
{
lean_ctor_set(v___x_1045_, 0, v___x_1049_);
v___x_1051_ = v___x_1045_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v___x_1049_);
v___x_1051_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
return v___x_1051_;
}
}
else
{
lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; 
lean_del_object(v___x_1045_);
v___x_1053_ = l_Lean_Expr_projExpr_x21(v_e_1028_);
v___x_1054_ = l_Lean_Expr_projIdx_x21(v_e_1028_);
lean_dec_ref(v_e_1028_);
v___x_1055_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___redArg(v___x_1053_, v___x_1054_);
lean_dec(v___x_1054_);
lean_dec_ref(v___x_1053_);
return v___x_1055_;
}
}
}
}
else
{
lean_object* v_a_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1080_; 
lean_dec_ref(v_e_1028_);
v_a_1073_ = lean_ctor_get(v___x_1042_, 0);
v_isSharedCheck_1080_ = !lean_is_exclusive(v___x_1042_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1075_ = v___x_1042_;
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_a_1073_);
lean_dec(v___x_1042_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1078_; 
if (v_isShared_1076_ == 0)
{
v___x_1078_ = v___x_1075_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_a_1073_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
return v___x_1078_;
}
}
}
v___jp_1034_:
{
lean_object* v___x_1036_; lean_object* v___x_1037_; 
v___x_1036_ = lean_unsigned_to_nat(0u);
v___x_1037_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___redArg(v_e_x27_1035_, v___x_1036_);
lean_dec_ref(v_e_x27_1035_);
return v___x_1037_;
}
v___jp_1038_:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1040_ = lean_unsigned_to_nat(1u);
v___x_1041_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___redArg(v_e_x27_1039_, v___x_1040_);
lean_dec_ref(v_e_x27_1039_);
return v___x_1041_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_reduceProjs___lam__1___boxed(lean_object* v_e_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_){
_start:
{
lean_object* v_res_1087_; 
v_res_1087_ = l_Lean_Meta_PProdN_reduceProjs___lam__1(v_e_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_);
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
return v_res_1087_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3_spec__4___redArg(lean_object* v_a_1088_, lean_object* v_x_1089_){
_start:
{
if (lean_obj_tag(v_x_1089_) == 0)
{
lean_object* v___x_1090_; 
v___x_1090_ = lean_box(0);
return v___x_1090_;
}
else
{
lean_object* v_key_1091_; lean_object* v_value_1092_; lean_object* v_tail_1093_; uint8_t v___x_1094_; 
v_key_1091_ = lean_ctor_get(v_x_1089_, 0);
v_value_1092_ = lean_ctor_get(v_x_1089_, 1);
v_tail_1093_ = lean_ctor_get(v_x_1089_, 2);
v___x_1094_ = l_Lean_ExprStructEq_beq(v_key_1091_, v_a_1088_);
if (v___x_1094_ == 0)
{
v_x_1089_ = v_tail_1093_;
goto _start;
}
else
{
lean_object* v___x_1096_; 
lean_inc(v_value_1092_);
v___x_1096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1096_, 0, v_value_1092_);
return v___x_1096_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object* v_a_1097_, lean_object* v_x_1098_){
_start:
{
lean_object* v_res_1099_; 
v_res_1099_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3_spec__4___redArg(v_a_1097_, v_x_1098_);
lean_dec(v_x_1098_);
lean_dec_ref(v_a_1097_);
return v_res_1099_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3___redArg(lean_object* v_m_1100_, lean_object* v_a_1101_){
_start:
{
lean_object* v_buckets_1102_; lean_object* v___x_1103_; uint64_t v___x_1104_; uint64_t v___x_1105_; uint64_t v___x_1106_; uint64_t v_fold_1107_; uint64_t v___x_1108_; uint64_t v___x_1109_; uint64_t v___x_1110_; size_t v___x_1111_; size_t v___x_1112_; size_t v___x_1113_; size_t v___x_1114_; size_t v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
v_buckets_1102_ = lean_ctor_get(v_m_1100_, 1);
v___x_1103_ = lean_array_get_size(v_buckets_1102_);
v___x_1104_ = l_Lean_ExprStructEq_hash(v_a_1101_);
v___x_1105_ = 32ULL;
v___x_1106_ = lean_uint64_shift_right(v___x_1104_, v___x_1105_);
v_fold_1107_ = lean_uint64_xor(v___x_1104_, v___x_1106_);
v___x_1108_ = 16ULL;
v___x_1109_ = lean_uint64_shift_right(v_fold_1107_, v___x_1108_);
v___x_1110_ = lean_uint64_xor(v_fold_1107_, v___x_1109_);
v___x_1111_ = lean_uint64_to_usize(v___x_1110_);
v___x_1112_ = lean_usize_of_nat(v___x_1103_);
v___x_1113_ = ((size_t)1ULL);
v___x_1114_ = lean_usize_sub(v___x_1112_, v___x_1113_);
v___x_1115_ = lean_usize_land(v___x_1111_, v___x_1114_);
v___x_1116_ = lean_array_uget_borrowed(v_buckets_1102_, v___x_1115_);
v___x_1117_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3_spec__4___redArg(v_a_1101_, v___x_1116_);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_m_1118_, lean_object* v_a_1119_){
_start:
{
lean_object* v_res_1120_; 
v_res_1120_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3___redArg(v_m_1118_, v_a_1119_);
lean_dec_ref(v_a_1119_);
lean_dec_ref(v_m_1118_);
return v_res_1120_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11___redArg(lean_object* v_a_1121_, lean_object* v_b_1122_, lean_object* v_x_1123_){
_start:
{
if (lean_obj_tag(v_x_1123_) == 0)
{
lean_dec(v_b_1122_);
lean_dec_ref(v_a_1121_);
return v_x_1123_;
}
else
{
lean_object* v_key_1124_; lean_object* v_value_1125_; lean_object* v_tail_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1138_; 
v_key_1124_ = lean_ctor_get(v_x_1123_, 0);
v_value_1125_ = lean_ctor_get(v_x_1123_, 1);
v_tail_1126_ = lean_ctor_get(v_x_1123_, 2);
v_isSharedCheck_1138_ = !lean_is_exclusive(v_x_1123_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1128_ = v_x_1123_;
v_isShared_1129_ = v_isSharedCheck_1138_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_tail_1126_);
lean_inc(v_value_1125_);
lean_inc(v_key_1124_);
lean_dec(v_x_1123_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1138_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
uint8_t v___x_1130_; 
v___x_1130_ = l_Lean_ExprStructEq_beq(v_key_1124_, v_a_1121_);
if (v___x_1130_ == 0)
{
lean_object* v___x_1131_; lean_object* v___x_1133_; 
v___x_1131_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11___redArg(v_a_1121_, v_b_1122_, v_tail_1126_);
if (v_isShared_1129_ == 0)
{
lean_ctor_set(v___x_1128_, 2, v___x_1131_);
v___x_1133_ = v___x_1128_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_key_1124_);
lean_ctor_set(v_reuseFailAlloc_1134_, 1, v_value_1125_);
lean_ctor_set(v_reuseFailAlloc_1134_, 2, v___x_1131_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
return v___x_1133_;
}
}
else
{
lean_object* v___x_1136_; 
lean_dec(v_value_1125_);
lean_dec(v_key_1124_);
if (v_isShared_1129_ == 0)
{
lean_ctor_set(v___x_1128_, 1, v_b_1122_);
lean_ctor_set(v___x_1128_, 0, v_a_1121_);
v___x_1136_ = v___x_1128_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_a_1121_);
lean_ctor_set(v_reuseFailAlloc_1137_, 1, v_b_1122_);
lean_ctor_set(v_reuseFailAlloc_1137_, 2, v_tail_1126_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__9___redArg(lean_object* v_a_1139_, lean_object* v_x_1140_){
_start:
{
if (lean_obj_tag(v_x_1140_) == 0)
{
uint8_t v___x_1141_; 
v___x_1141_ = 0;
return v___x_1141_;
}
else
{
lean_object* v_key_1142_; lean_object* v_tail_1143_; uint8_t v___x_1144_; 
v_key_1142_ = lean_ctor_get(v_x_1140_, 0);
v_tail_1143_ = lean_ctor_get(v_x_1140_, 2);
v___x_1144_ = l_Lean_ExprStructEq_beq(v_key_1142_, v_a_1139_);
if (v___x_1144_ == 0)
{
v_x_1140_ = v_tail_1143_;
goto _start;
}
else
{
return v___x_1144_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__9___redArg___boxed(lean_object* v_a_1146_, lean_object* v_x_1147_){
_start:
{
uint8_t v_res_1148_; lean_object* v_r_1149_; 
v_res_1148_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__9___redArg(v_a_1146_, v_x_1147_);
lean_dec(v_x_1147_);
lean_dec_ref(v_a_1146_);
v_r_1149_ = lean_box(v_res_1148_);
return v_r_1149_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12___redArg(lean_object* v_x_1150_, lean_object* v_x_1151_){
_start:
{
if (lean_obj_tag(v_x_1151_) == 0)
{
return v_x_1150_;
}
else
{
lean_object* v_key_1152_; lean_object* v_value_1153_; lean_object* v_tail_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1177_; 
v_key_1152_ = lean_ctor_get(v_x_1151_, 0);
v_value_1153_ = lean_ctor_get(v_x_1151_, 1);
v_tail_1154_ = lean_ctor_get(v_x_1151_, 2);
v_isSharedCheck_1177_ = !lean_is_exclusive(v_x_1151_);
if (v_isSharedCheck_1177_ == 0)
{
v___x_1156_ = v_x_1151_;
v_isShared_1157_ = v_isSharedCheck_1177_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_tail_1154_);
lean_inc(v_value_1153_);
lean_inc(v_key_1152_);
lean_dec(v_x_1151_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1177_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v___x_1158_; uint64_t v___x_1159_; uint64_t v___x_1160_; uint64_t v___x_1161_; uint64_t v_fold_1162_; uint64_t v___x_1163_; uint64_t v___x_1164_; uint64_t v___x_1165_; size_t v___x_1166_; size_t v___x_1167_; size_t v___x_1168_; size_t v___x_1169_; size_t v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1173_; 
v___x_1158_ = lean_array_get_size(v_x_1150_);
v___x_1159_ = l_Lean_ExprStructEq_hash(v_key_1152_);
v___x_1160_ = 32ULL;
v___x_1161_ = lean_uint64_shift_right(v___x_1159_, v___x_1160_);
v_fold_1162_ = lean_uint64_xor(v___x_1159_, v___x_1161_);
v___x_1163_ = 16ULL;
v___x_1164_ = lean_uint64_shift_right(v_fold_1162_, v___x_1163_);
v___x_1165_ = lean_uint64_xor(v_fold_1162_, v___x_1164_);
v___x_1166_ = lean_uint64_to_usize(v___x_1165_);
v___x_1167_ = lean_usize_of_nat(v___x_1158_);
v___x_1168_ = ((size_t)1ULL);
v___x_1169_ = lean_usize_sub(v___x_1167_, v___x_1168_);
v___x_1170_ = lean_usize_land(v___x_1166_, v___x_1169_);
v___x_1171_ = lean_array_uget_borrowed(v_x_1150_, v___x_1170_);
lean_inc(v___x_1171_);
if (v_isShared_1157_ == 0)
{
lean_ctor_set(v___x_1156_, 2, v___x_1171_);
v___x_1173_ = v___x_1156_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v_key_1152_);
lean_ctor_set(v_reuseFailAlloc_1176_, 1, v_value_1153_);
lean_ctor_set(v_reuseFailAlloc_1176_, 2, v___x_1171_);
v___x_1173_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
lean_object* v___x_1174_; 
v___x_1174_ = lean_array_uset(v_x_1150_, v___x_1170_, v___x_1173_);
v_x_1150_ = v___x_1174_;
v_x_1151_ = v_tail_1154_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__10_spec__11___redArg(lean_object* v_i_1178_, lean_object* v_source_1179_, lean_object* v_target_1180_){
_start:
{
lean_object* v___x_1181_; uint8_t v___x_1182_; 
v___x_1181_ = lean_array_get_size(v_source_1179_);
v___x_1182_ = lean_nat_dec_lt(v_i_1178_, v___x_1181_);
if (v___x_1182_ == 0)
{
lean_dec_ref(v_source_1179_);
lean_dec(v_i_1178_);
return v_target_1180_;
}
else
{
lean_object* v_es_1183_; lean_object* v___x_1184_; lean_object* v_source_1185_; lean_object* v_target_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; 
v_es_1183_ = lean_array_fget(v_source_1179_, v_i_1178_);
v___x_1184_ = lean_box(0);
v_source_1185_ = lean_array_fset(v_source_1179_, v_i_1178_, v___x_1184_);
v_target_1186_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12___redArg(v_target_1180_, v_es_1183_);
v___x_1187_ = lean_unsigned_to_nat(1u);
v___x_1188_ = lean_nat_add(v_i_1178_, v___x_1187_);
lean_dec(v_i_1178_);
v_i_1178_ = v___x_1188_;
v_source_1179_ = v_source_1185_;
v_target_1180_ = v_target_1186_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__10___redArg(lean_object* v_data_1190_){
_start:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v_nbuckets_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1191_ = lean_array_get_size(v_data_1190_);
v___x_1192_ = lean_unsigned_to_nat(2u);
v_nbuckets_1193_ = lean_nat_mul(v___x_1191_, v___x_1192_);
v___x_1194_ = lean_unsigned_to_nat(0u);
v___x_1195_ = lean_box(0);
v___x_1196_ = lean_mk_array(v_nbuckets_1193_, v___x_1195_);
v___x_1197_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__10_spec__11___redArg(v___x_1194_, v_data_1190_, v___x_1196_);
return v___x_1197_;
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
v___x_1220_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__9___redArg(v_a_1199_, v_bkt_1219_);
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
v_val_1231_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__10___redArg(v_buckets_x27_1224_);
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
v___x_1240_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11___redArg(v_a_1199_, v_b_1200_, v_bkt_1219_);
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
v___x_1251_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6___redArg(v___x_1250_, v_e_1247_, v_a_1248_);
v___x_1252_ = lean_st_ref_set(v_a_1246_, v___x_1251_);
v___x_1253_ = lean_box(0);
return v___x_1253_;
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
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1281_ = l_Lean_maxRecDepthErrorMessage;
v___x_1282_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1282_, 0, v___x_1281_);
return v___x_1282_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1283_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__3);
v___x_1284_ = l_Lean_MessageData_ofFormat(v___x_1283_);
return v___x_1284_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1285_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__4);
v___x_1286_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__2));
v___x_1287_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1287_, 0, v___x_1286_);
lean_ctor_set(v___x_1287_, 1, v___x_1285_);
return v___x_1287_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg(lean_object* v_ref_1288_){
_start:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1290_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__5);
v___x_1291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1291_, 0, v_ref_1288_);
lean_ctor_set(v___x_1291_, 1, v___x_1290_);
v___x_1292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1292_, 0, v___x_1291_);
return v___x_1292_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object* v_ref_1293_, lean_object* v___y_1294_){
_start:
{
lean_object* v_res_1295_; 
v_res_1295_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_1293_);
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5___redArg(lean_object* v_x_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_){
_start:
{
lean_object* v___y_1304_; lean_object* v_fileName_1313_; lean_object* v_fileMap_1314_; lean_object* v_options_1315_; lean_object* v_currRecDepth_1316_; lean_object* v_maxRecDepth_1317_; lean_object* v_ref_1318_; lean_object* v_currNamespace_1319_; lean_object* v_openDecls_1320_; lean_object* v_initHeartbeats_1321_; lean_object* v_maxHeartbeats_1322_; lean_object* v_quotContext_1323_; lean_object* v_currMacroScope_1324_; uint8_t v_diag_1325_; lean_object* v_cancelTk_x3f_1326_; uint8_t v_suppressElabErrors_1327_; lean_object* v_inheritedTraceOptions_1328_; uint8_t v___x_1329_; 
v_fileName_1313_ = lean_ctor_get(v___y_1300_, 0);
v_fileMap_1314_ = lean_ctor_get(v___y_1300_, 1);
v_options_1315_ = lean_ctor_get(v___y_1300_, 2);
v_currRecDepth_1316_ = lean_ctor_get(v___y_1300_, 3);
v_maxRecDepth_1317_ = lean_ctor_get(v___y_1300_, 4);
v_ref_1318_ = lean_ctor_get(v___y_1300_, 5);
v_currNamespace_1319_ = lean_ctor_get(v___y_1300_, 6);
v_openDecls_1320_ = lean_ctor_get(v___y_1300_, 7);
v_initHeartbeats_1321_ = lean_ctor_get(v___y_1300_, 8);
v_maxHeartbeats_1322_ = lean_ctor_get(v___y_1300_, 9);
v_quotContext_1323_ = lean_ctor_get(v___y_1300_, 10);
v_currMacroScope_1324_ = lean_ctor_get(v___y_1300_, 11);
v_diag_1325_ = lean_ctor_get_uint8(v___y_1300_, sizeof(void*)*14);
v_cancelTk_x3f_1326_ = lean_ctor_get(v___y_1300_, 12);
v_suppressElabErrors_1327_ = lean_ctor_get_uint8(v___y_1300_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1328_ = lean_ctor_get(v___y_1300_, 13);
v___x_1329_ = lean_nat_dec_eq(v_currRecDepth_1316_, v_maxRecDepth_1317_);
if (v___x_1329_ == 0)
{
lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1330_ = lean_unsigned_to_nat(1u);
v___x_1331_ = lean_nat_add(v_currRecDepth_1316_, v___x_1330_);
lean_inc_ref(v_inheritedTraceOptions_1328_);
lean_inc(v_cancelTk_x3f_1326_);
lean_inc(v_currMacroScope_1324_);
lean_inc(v_quotContext_1323_);
lean_inc(v_maxHeartbeats_1322_);
lean_inc(v_initHeartbeats_1321_);
lean_inc(v_openDecls_1320_);
lean_inc(v_currNamespace_1319_);
lean_inc(v_ref_1318_);
lean_inc(v_maxRecDepth_1317_);
lean_inc_ref(v_options_1315_);
lean_inc_ref(v_fileMap_1314_);
lean_inc_ref(v_fileName_1313_);
v___x_1332_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1332_, 0, v_fileName_1313_);
lean_ctor_set(v___x_1332_, 1, v_fileMap_1314_);
lean_ctor_set(v___x_1332_, 2, v_options_1315_);
lean_ctor_set(v___x_1332_, 3, v___x_1331_);
lean_ctor_set(v___x_1332_, 4, v_maxRecDepth_1317_);
lean_ctor_set(v___x_1332_, 5, v_ref_1318_);
lean_ctor_set(v___x_1332_, 6, v_currNamespace_1319_);
lean_ctor_set(v___x_1332_, 7, v_openDecls_1320_);
lean_ctor_set(v___x_1332_, 8, v_initHeartbeats_1321_);
lean_ctor_set(v___x_1332_, 9, v_maxHeartbeats_1322_);
lean_ctor_set(v___x_1332_, 10, v_quotContext_1323_);
lean_ctor_set(v___x_1332_, 11, v_currMacroScope_1324_);
lean_ctor_set(v___x_1332_, 12, v_cancelTk_x3f_1326_);
lean_ctor_set(v___x_1332_, 13, v_inheritedTraceOptions_1328_);
lean_ctor_set_uint8(v___x_1332_, sizeof(void*)*14, v_diag_1325_);
lean_ctor_set_uint8(v___x_1332_, sizeof(void*)*14 + 1, v_suppressElabErrors_1327_);
lean_inc(v___y_1301_);
lean_inc(v___y_1299_);
lean_inc_ref(v___y_1298_);
lean_inc(v___y_1297_);
v___x_1333_ = lean_apply_6(v_x_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___x_1332_, v___y_1301_, lean_box(0));
v___y_1304_ = v___x_1333_;
goto v___jp_1303_;
}
else
{
lean_object* v___x_1334_; 
lean_dec_ref(v_x_1296_);
lean_inc(v_ref_1318_);
v___x_1334_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_1318_);
v___y_1304_ = v___x_1334_;
goto v___jp_1303_;
}
v___jp_1303_:
{
if (lean_obj_tag(v___y_1304_) == 0)
{
return v___y_1304_;
}
else
{
lean_object* v_a_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1312_; 
v_a_1305_ = lean_ctor_get(v___y_1304_, 0);
v_isSharedCheck_1312_ = !lean_is_exclusive(v___y_1304_);
if (v_isSharedCheck_1312_ == 0)
{
v___x_1307_ = v___y_1304_;
v_isShared_1308_ = v_isSharedCheck_1312_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_a_1305_);
lean_dec(v___y_1304_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1312_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v___x_1310_; 
if (v_isShared_1308_ == 0)
{
v___x_1310_ = v___x_1307_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v_a_1305_);
v___x_1310_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
return v___x_1310_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_x_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_){
_start:
{
lean_object* v_res_1342_; 
v_res_1342_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5___redArg(v_x_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_);
lean_dec(v___y_1340_);
lean_dec_ref(v___y_1339_);
lean_dec(v___y_1338_);
lean_dec_ref(v___y_1337_);
lean_dec(v___y_1336_);
return v_res_1342_;
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__1___closed__0(void){
_start:
{
lean_object* v___x_1343_; lean_object* v_dummy_1344_; 
v___x_1343_ = lean_box(0);
v_dummy_1344_ = l_Lean_Expr_sort___override(v___x_1343_);
return v_dummy_1344_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__1(lean_object* v_pre_1345_, lean_object* v_post_1346_, size_t v_sz_1347_, size_t v_i_1348_, lean_object* v_bs_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_){
_start:
{
uint8_t v___x_1356_; 
v___x_1356_ = lean_usize_dec_lt(v_i_1348_, v_sz_1347_);
if (v___x_1356_ == 0)
{
lean_object* v___x_1357_; 
lean_dec_ref(v_post_1346_);
lean_dec_ref(v_pre_1345_);
v___x_1357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1357_, 0, v_bs_1349_);
return v___x_1357_;
}
else
{
lean_object* v_v_1358_; lean_object* v___x_1359_; 
v_v_1358_ = lean_array_uget_borrowed(v_bs_1349_, v_i_1348_);
lean_inc(v_v_1358_);
lean_inc_ref(v_post_1346_);
lean_inc_ref(v_pre_1345_);
v___x_1359_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1345_, v_post_1346_, v_v_1358_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_);
if (lean_obj_tag(v___x_1359_) == 0)
{
lean_object* v_a_1360_; lean_object* v___x_1361_; lean_object* v_bs_x27_1362_; size_t v___x_1363_; size_t v___x_1364_; lean_object* v___x_1365_; 
v_a_1360_ = lean_ctor_get(v___x_1359_, 0);
lean_inc(v_a_1360_);
lean_dec_ref(v___x_1359_);
v___x_1361_ = lean_unsigned_to_nat(0u);
v_bs_x27_1362_ = lean_array_uset(v_bs_1349_, v_i_1348_, v___x_1361_);
v___x_1363_ = ((size_t)1ULL);
v___x_1364_ = lean_usize_add(v_i_1348_, v___x_1363_);
v___x_1365_ = lean_array_uset(v_bs_x27_1362_, v_i_1348_, v_a_1360_);
v_i_1348_ = v___x_1364_;
v_bs_1349_ = v___x_1365_;
goto _start;
}
else
{
lean_object* v_a_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1374_; 
lean_dec_ref(v_bs_1349_);
lean_dec_ref(v_post_1346_);
lean_dec_ref(v_pre_1345_);
v_a_1367_ = lean_ctor_get(v___x_1359_, 0);
v_isSharedCheck_1374_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1374_ == 0)
{
v___x_1369_ = v___x_1359_;
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_a_1367_);
lean_dec(v___x_1359_);
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
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__4(lean_object* v_pre_1375_, lean_object* v_post_1376_, lean_object* v_x_1377_, lean_object* v_x_1378_, lean_object* v_x_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_){
_start:
{
if (lean_obj_tag(v_x_1377_) == 5)
{
lean_object* v_fn_1386_; lean_object* v_arg_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; 
v_fn_1386_ = lean_ctor_get(v_x_1377_, 0);
lean_inc_ref(v_fn_1386_);
v_arg_1387_ = lean_ctor_get(v_x_1377_, 1);
lean_inc_ref(v_arg_1387_);
lean_dec_ref(v_x_1377_);
v___x_1388_ = lean_array_set(v_x_1378_, v_x_1379_, v_arg_1387_);
v___x_1389_ = lean_unsigned_to_nat(1u);
v___x_1390_ = lean_nat_sub(v_x_1379_, v___x_1389_);
lean_dec(v_x_1379_);
v_x_1377_ = v_fn_1386_;
v_x_1378_ = v___x_1388_;
v_x_1379_ = v___x_1390_;
goto _start;
}
else
{
lean_object* v___x_1392_; 
lean_dec(v_x_1379_);
lean_inc_ref(v_post_1376_);
lean_inc_ref(v_pre_1375_);
v___x_1392_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1375_, v_post_1376_, v_x_1377_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_);
if (lean_obj_tag(v___x_1392_) == 0)
{
lean_object* v_a_1393_; size_t v_sz_1394_; size_t v___x_1395_; lean_object* v___x_1396_; 
v_a_1393_ = lean_ctor_get(v___x_1392_, 0);
lean_inc(v_a_1393_);
lean_dec_ref(v___x_1392_);
v_sz_1394_ = lean_array_size(v_x_1378_);
v___x_1395_ = ((size_t)0ULL);
lean_inc_ref(v_post_1376_);
lean_inc_ref(v_pre_1375_);
v___x_1396_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__1(v_pre_1375_, v_post_1376_, v_sz_1394_, v___x_1395_, v_x_1378_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_);
if (lean_obj_tag(v___x_1396_) == 0)
{
lean_object* v_a_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; 
v_a_1397_ = lean_ctor_get(v___x_1396_, 0);
lean_inc(v_a_1397_);
lean_dec_ref(v___x_1396_);
v___x_1398_ = l_Lean_mkAppN(v_a_1393_, v_a_1397_);
lean_dec(v_a_1397_);
v___x_1399_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1375_, v_post_1376_, v___x_1398_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_);
return v___x_1399_;
}
else
{
lean_object* v_a_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1407_; 
lean_dec(v_a_1393_);
lean_dec_ref(v_post_1376_);
lean_dec_ref(v_pre_1375_);
v_a_1400_ = lean_ctor_get(v___x_1396_, 0);
v_isSharedCheck_1407_ = !lean_is_exclusive(v___x_1396_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1402_ = v___x_1396_;
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_a_1400_);
lean_dec(v___x_1396_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1405_; 
if (v_isShared_1403_ == 0)
{
v___x_1405_ = v___x_1402_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v_a_1400_);
v___x_1405_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
return v___x_1405_;
}
}
}
}
else
{
lean_dec_ref(v_x_1378_);
lean_dec_ref(v_post_1376_);
lean_dec_ref(v_pre_1375_);
return v___x_1392_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__1(lean_object* v_pre_1408_, lean_object* v_e_1409_, lean_object* v_post_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_){
_start:
{
lean_object* v___y_1418_; lean_object* v___y_1419_; lean_object* v___y_1420_; lean_object* v___y_1421_; uint8_t v___y_1422_; lean_object* v___y_1423_; lean_object* v___y_1424_; uint8_t v___y_1425_; lean_object* v___y_1435_; lean_object* v___y_1436_; uint8_t v___y_1437_; lean_object* v___y_1438_; lean_object* v___y_1439_; uint8_t v___y_1440_; lean_object* v___y_1448_; uint8_t v___y_1449_; lean_object* v___y_1450_; lean_object* v___y_1451_; lean_object* v___y_1452_; uint8_t v___y_1453_; lean_object* v___x_1460_; 
lean_inc_ref(v_pre_1408_);
lean_inc(v___y_1415_);
lean_inc_ref(v___y_1414_);
lean_inc(v___y_1413_);
lean_inc_ref(v___y_1412_);
lean_inc_ref(v_e_1409_);
v___x_1460_ = lean_apply_6(v_pre_1408_, v_e_1409_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_, lean_box(0));
if (lean_obj_tag(v___x_1460_) == 0)
{
lean_object* v_a_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1550_; 
v_a_1461_ = lean_ctor_get(v___x_1460_, 0);
v_isSharedCheck_1550_ = !lean_is_exclusive(v___x_1460_);
if (v_isSharedCheck_1550_ == 0)
{
v___x_1463_ = v___x_1460_;
v_isShared_1464_ = v_isSharedCheck_1550_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_a_1461_);
lean_dec(v___x_1460_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1550_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v___y_1466_; 
switch(lean_obj_tag(v_a_1461_))
{
case 0:
{
lean_object* v_e_1540_; lean_object* v___x_1542_; 
lean_dec_ref(v_post_1410_);
lean_dec_ref(v_e_1409_);
lean_dec_ref(v_pre_1408_);
v_e_1540_ = lean_ctor_get(v_a_1461_, 0);
lean_inc_ref(v_e_1540_);
lean_dec_ref(v_a_1461_);
if (v_isShared_1464_ == 0)
{
lean_ctor_set(v___x_1463_, 0, v_e_1540_);
v___x_1542_ = v___x_1463_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v_e_1540_);
v___x_1542_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
return v___x_1542_;
}
}
case 1:
{
lean_object* v_e_1544_; lean_object* v___x_1545_; 
lean_del_object(v___x_1463_);
lean_dec_ref(v_e_1409_);
v_e_1544_ = lean_ctor_get(v_a_1461_, 0);
lean_inc_ref(v_e_1544_);
lean_dec_ref(v_a_1461_);
lean_inc_ref(v_post_1410_);
lean_inc_ref(v_pre_1408_);
v___x_1545_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1408_, v_post_1410_, v_e_1544_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v_a_1546_; lean_object* v___x_1547_; 
v_a_1546_ = lean_ctor_get(v___x_1545_, 0);
lean_inc(v_a_1546_);
lean_dec_ref(v___x_1545_);
v___x_1547_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1408_, v_post_1410_, v_a_1546_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
return v___x_1547_;
}
else
{
lean_dec_ref(v_post_1410_);
lean_dec_ref(v_pre_1408_);
return v___x_1545_;
}
}
default: 
{
lean_object* v_e_x3f_1548_; 
lean_del_object(v___x_1463_);
v_e_x3f_1548_ = lean_ctor_get(v_a_1461_, 0);
lean_inc(v_e_x3f_1548_);
lean_dec_ref(v_a_1461_);
if (lean_obj_tag(v_e_x3f_1548_) == 0)
{
v___y_1466_ = v_e_1409_;
goto v___jp_1465_;
}
else
{
lean_object* v_val_1549_; 
lean_dec_ref(v_e_1409_);
v_val_1549_ = lean_ctor_get(v_e_x3f_1548_, 0);
lean_inc(v_val_1549_);
lean_dec_ref(v_e_x3f_1548_);
v___y_1466_ = v_val_1549_;
goto v___jp_1465_;
}
}
}
v___jp_1465_:
{
switch(lean_obj_tag(v___y_1466_))
{
case 7:
{
lean_object* v_binderName_1467_; lean_object* v_binderType_1468_; lean_object* v_body_1469_; uint8_t v_binderInfo_1470_; lean_object* v___x_1471_; 
v_binderName_1467_ = lean_ctor_get(v___y_1466_, 0);
lean_inc(v_binderName_1467_);
v_binderType_1468_ = lean_ctor_get(v___y_1466_, 1);
v_body_1469_ = lean_ctor_get(v___y_1466_, 2);
v_binderInfo_1470_ = lean_ctor_get_uint8(v___y_1466_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1468_);
lean_inc_ref(v_post_1410_);
lean_inc_ref(v_pre_1408_);
v___x_1471_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1408_, v_post_1410_, v_binderType_1468_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
if (lean_obj_tag(v___x_1471_) == 0)
{
lean_object* v_a_1472_; lean_object* v___x_1473_; 
v_a_1472_ = lean_ctor_get(v___x_1471_, 0);
lean_inc(v_a_1472_);
lean_dec_ref(v___x_1471_);
lean_inc_ref(v_body_1469_);
lean_inc_ref(v_post_1410_);
lean_inc_ref(v_pre_1408_);
v___x_1473_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1408_, v_post_1410_, v_body_1469_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
if (lean_obj_tag(v___x_1473_) == 0)
{
lean_object* v_a_1474_; size_t v___x_1475_; size_t v___x_1476_; uint8_t v___x_1477_; 
v_a_1474_ = lean_ctor_get(v___x_1473_, 0);
lean_inc(v_a_1474_);
lean_dec_ref(v___x_1473_);
v___x_1475_ = lean_ptr_addr(v_binderType_1468_);
v___x_1476_ = lean_ptr_addr(v_a_1472_);
v___x_1477_ = lean_usize_dec_eq(v___x_1475_, v___x_1476_);
if (v___x_1477_ == 0)
{
v___y_1448_ = v_a_1472_;
v___y_1449_ = v_binderInfo_1470_;
v___y_1450_ = v_a_1474_;
v___y_1451_ = v_binderName_1467_;
v___y_1452_ = v___y_1466_;
v___y_1453_ = v___x_1477_;
goto v___jp_1447_;
}
else
{
size_t v___x_1478_; size_t v___x_1479_; uint8_t v___x_1480_; 
v___x_1478_ = lean_ptr_addr(v_body_1469_);
v___x_1479_ = lean_ptr_addr(v_a_1474_);
v___x_1480_ = lean_usize_dec_eq(v___x_1478_, v___x_1479_);
v___y_1448_ = v_a_1472_;
v___y_1449_ = v_binderInfo_1470_;
v___y_1450_ = v_a_1474_;
v___y_1451_ = v_binderName_1467_;
v___y_1452_ = v___y_1466_;
v___y_1453_ = v___x_1480_;
goto v___jp_1447_;
}
}
else
{
lean_dec(v_a_1472_);
lean_dec(v_binderName_1467_);
lean_dec_ref(v___y_1466_);
lean_dec_ref(v_post_1410_);
lean_dec_ref(v_pre_1408_);
return v___x_1473_;
}
}
else
{
lean_dec(v_binderName_1467_);
lean_dec_ref(v___y_1466_);
lean_dec_ref(v_post_1410_);
lean_dec_ref(v_pre_1408_);
return v___x_1471_;
}
}
case 6:
{
lean_object* v_binderName_1481_; lean_object* v_binderType_1482_; lean_object* v_body_1483_; uint8_t v_binderInfo_1484_; lean_object* v___x_1485_; 
v_binderName_1481_ = lean_ctor_get(v___y_1466_, 0);
lean_inc(v_binderName_1481_);
v_binderType_1482_ = lean_ctor_get(v___y_1466_, 1);
v_body_1483_ = lean_ctor_get(v___y_1466_, 2);
v_binderInfo_1484_ = lean_ctor_get_uint8(v___y_1466_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1482_);
lean_inc_ref(v_post_1410_);
lean_inc_ref(v_pre_1408_);
v___x_1485_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1408_, v_post_1410_, v_binderType_1482_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
if (lean_obj_tag(v___x_1485_) == 0)
{
lean_object* v_a_1486_; lean_object* v___x_1487_; 
v_a_1486_ = lean_ctor_get(v___x_1485_, 0);
lean_inc(v_a_1486_);
lean_dec_ref(v___x_1485_);
lean_inc_ref(v_body_1483_);
lean_inc_ref(v_post_1410_);
lean_inc_ref(v_pre_1408_);
v___x_1487_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1408_, v_post_1410_, v_body_1483_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
if (lean_obj_tag(v___x_1487_) == 0)
{
lean_object* v_a_1488_; size_t v___x_1489_; size_t v___x_1490_; uint8_t v___x_1491_; 
v_a_1488_ = lean_ctor_get(v___x_1487_, 0);
lean_inc(v_a_1488_);
lean_dec_ref(v___x_1487_);
v___x_1489_ = lean_ptr_addr(v_binderType_1482_);
v___x_1490_ = lean_ptr_addr(v_a_1486_);
v___x_1491_ = lean_usize_dec_eq(v___x_1489_, v___x_1490_);
if (v___x_1491_ == 0)
{
v___y_1435_ = v_a_1488_;
v___y_1436_ = v_a_1486_;
v___y_1437_ = v_binderInfo_1484_;
v___y_1438_ = v_binderName_1481_;
v___y_1439_ = v___y_1466_;
v___y_1440_ = v___x_1491_;
goto v___jp_1434_;
}
else
{
size_t v___x_1492_; size_t v___x_1493_; uint8_t v___x_1494_; 
v___x_1492_ = lean_ptr_addr(v_body_1483_);
v___x_1493_ = lean_ptr_addr(v_a_1488_);
v___x_1494_ = lean_usize_dec_eq(v___x_1492_, v___x_1493_);
v___y_1435_ = v_a_1488_;
v___y_1436_ = v_a_1486_;
v___y_1437_ = v_binderInfo_1484_;
v___y_1438_ = v_binderName_1481_;
v___y_1439_ = v___y_1466_;
v___y_1440_ = v___x_1494_;
goto v___jp_1434_;
}
}
else
{
lean_dec(v_a_1486_);
lean_dec_ref(v___y_1466_);
lean_dec(v_binderName_1481_);
lean_dec_ref(v_post_1410_);
lean_dec_ref(v_pre_1408_);
return v___x_1487_;
}
}
else
{
lean_dec_ref(v___y_1466_);
lean_dec(v_binderName_1481_);
lean_dec_ref(v_post_1410_);
lean_dec_ref(v_pre_1408_);
return v___x_1485_;
}
}
case 8:
{
lean_object* v_declName_1495_; lean_object* v_type_1496_; lean_object* v_value_1497_; lean_object* v_body_1498_; uint8_t v_nondep_1499_; lean_object* v___x_1500_; 
v_declName_1495_ = lean_ctor_get(v___y_1466_, 0);
lean_inc(v_declName_1495_);
v_type_1496_ = lean_ctor_get(v___y_1466_, 1);
v_value_1497_ = lean_ctor_get(v___y_1466_, 2);
v_body_1498_ = lean_ctor_get(v___y_1466_, 3);
lean_inc_ref(v_body_1498_);
v_nondep_1499_ = lean_ctor_get_uint8(v___y_1466_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_1496_);
lean_inc_ref(v_post_1410_);
lean_inc_ref(v_pre_1408_);
v___x_1500_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1408_, v_post_1410_, v_type_1496_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
if (lean_obj_tag(v___x_1500_) == 0)
{
lean_object* v_a_1501_; lean_object* v___x_1502_; 
v_a_1501_ = lean_ctor_get(v___x_1500_, 0);
lean_inc(v_a_1501_);
lean_dec_ref(v___x_1500_);
lean_inc_ref(v_value_1497_);
lean_inc_ref(v_post_1410_);
lean_inc_ref(v_pre_1408_);
v___x_1502_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1408_, v_post_1410_, v_value_1497_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
if (lean_obj_tag(v___x_1502_) == 0)
{
lean_object* v_a_1503_; lean_object* v___x_1504_; 
v_a_1503_ = lean_ctor_get(v___x_1502_, 0);
lean_inc(v_a_1503_);
lean_dec_ref(v___x_1502_);
lean_inc_ref(v_body_1498_);
lean_inc_ref(v_post_1410_);
lean_inc_ref(v_pre_1408_);
v___x_1504_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1408_, v_post_1410_, v_body_1498_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
if (lean_obj_tag(v___x_1504_) == 0)
{
lean_object* v_a_1505_; size_t v___x_1506_; size_t v___x_1507_; uint8_t v___x_1508_; 
v_a_1505_ = lean_ctor_get(v___x_1504_, 0);
lean_inc(v_a_1505_);
lean_dec_ref(v___x_1504_);
v___x_1506_ = lean_ptr_addr(v_type_1496_);
v___x_1507_ = lean_ptr_addr(v_a_1501_);
v___x_1508_ = lean_usize_dec_eq(v___x_1506_, v___x_1507_);
if (v___x_1508_ == 0)
{
v___y_1418_ = v_a_1505_;
v___y_1419_ = v_a_1501_;
v___y_1420_ = v_body_1498_;
v___y_1421_ = v_a_1503_;
v___y_1422_ = v_nondep_1499_;
v___y_1423_ = v___y_1466_;
v___y_1424_ = v_declName_1495_;
v___y_1425_ = v___x_1508_;
goto v___jp_1417_;
}
else
{
size_t v___x_1509_; size_t v___x_1510_; uint8_t v___x_1511_; 
v___x_1509_ = lean_ptr_addr(v_value_1497_);
v___x_1510_ = lean_ptr_addr(v_a_1503_);
v___x_1511_ = lean_usize_dec_eq(v___x_1509_, v___x_1510_);
v___y_1418_ = v_a_1505_;
v___y_1419_ = v_a_1501_;
v___y_1420_ = v_body_1498_;
v___y_1421_ = v_a_1503_;
v___y_1422_ = v_nondep_1499_;
v___y_1423_ = v___y_1466_;
v___y_1424_ = v_declName_1495_;
v___y_1425_ = v___x_1511_;
goto v___jp_1417_;
}
}
else
{
lean_dec(v_a_1503_);
lean_dec(v_a_1501_);
lean_dec_ref(v_body_1498_);
lean_dec(v_declName_1495_);
lean_dec_ref(v___y_1466_);
lean_dec_ref(v_post_1410_);
lean_dec_ref(v_pre_1408_);
return v___x_1504_;
}
}
else
{
lean_dec(v_a_1501_);
lean_dec_ref(v_body_1498_);
lean_dec_ref(v___y_1466_);
lean_dec(v_declName_1495_);
lean_dec_ref(v_post_1410_);
lean_dec_ref(v_pre_1408_);
return v___x_1502_;
}
}
else
{
lean_dec_ref(v_body_1498_);
lean_dec(v_declName_1495_);
lean_dec_ref(v___y_1466_);
lean_dec_ref(v_post_1410_);
lean_dec_ref(v_pre_1408_);
return v___x_1500_;
}
}
case 5:
{
lean_object* v_dummy_1512_; lean_object* v_nargs_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; 
v_dummy_1512_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__1___closed__0);
v_nargs_1513_ = l_Lean_Expr_getAppNumArgs(v___y_1466_);
lean_inc(v_nargs_1513_);
v___x_1514_ = lean_mk_array(v_nargs_1513_, v_dummy_1512_);
v___x_1515_ = lean_unsigned_to_nat(1u);
v___x_1516_ = lean_nat_sub(v_nargs_1513_, v___x_1515_);
lean_dec(v_nargs_1513_);
v___x_1517_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__4(v_pre_1408_, v_post_1410_, v___y_1466_, v___x_1514_, v___x_1516_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
return v___x_1517_;
}
case 10:
{
lean_object* v_data_1518_; lean_object* v_expr_1519_; lean_object* v___x_1520_; 
v_data_1518_ = lean_ctor_get(v___y_1466_, 0);
v_expr_1519_ = lean_ctor_get(v___y_1466_, 1);
lean_inc_ref(v_expr_1519_);
lean_inc_ref(v_post_1410_);
lean_inc_ref(v_pre_1408_);
v___x_1520_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1408_, v_post_1410_, v_expr_1519_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
if (lean_obj_tag(v___x_1520_) == 0)
{
lean_object* v_a_1521_; size_t v___x_1522_; size_t v___x_1523_; uint8_t v___x_1524_; 
v_a_1521_ = lean_ctor_get(v___x_1520_, 0);
lean_inc(v_a_1521_);
lean_dec_ref(v___x_1520_);
v___x_1522_ = lean_ptr_addr(v_expr_1519_);
v___x_1523_ = lean_ptr_addr(v_a_1521_);
v___x_1524_ = lean_usize_dec_eq(v___x_1522_, v___x_1523_);
if (v___x_1524_ == 0)
{
lean_object* v___x_1525_; lean_object* v___x_1526_; 
lean_inc(v_data_1518_);
lean_dec_ref(v___y_1466_);
v___x_1525_ = l_Lean_Expr_mdata___override(v_data_1518_, v_a_1521_);
v___x_1526_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1408_, v_post_1410_, v___x_1525_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
return v___x_1526_;
}
else
{
lean_object* v___x_1527_; 
lean_dec(v_a_1521_);
v___x_1527_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1408_, v_post_1410_, v___y_1466_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
return v___x_1527_;
}
}
else
{
lean_dec_ref(v___y_1466_);
lean_dec_ref(v_post_1410_);
lean_dec_ref(v_pre_1408_);
return v___x_1520_;
}
}
case 11:
{
lean_object* v_typeName_1528_; lean_object* v_idx_1529_; lean_object* v_struct_1530_; lean_object* v___x_1531_; 
v_typeName_1528_ = lean_ctor_get(v___y_1466_, 0);
v_idx_1529_ = lean_ctor_get(v___y_1466_, 1);
v_struct_1530_ = lean_ctor_get(v___y_1466_, 2);
lean_inc_ref(v_struct_1530_);
lean_inc_ref(v_post_1410_);
lean_inc_ref(v_pre_1408_);
v___x_1531_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1408_, v_post_1410_, v_struct_1530_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
if (lean_obj_tag(v___x_1531_) == 0)
{
lean_object* v_a_1532_; size_t v___x_1533_; size_t v___x_1534_; uint8_t v___x_1535_; 
v_a_1532_ = lean_ctor_get(v___x_1531_, 0);
lean_inc(v_a_1532_);
lean_dec_ref(v___x_1531_);
v___x_1533_ = lean_ptr_addr(v_struct_1530_);
v___x_1534_ = lean_ptr_addr(v_a_1532_);
v___x_1535_ = lean_usize_dec_eq(v___x_1533_, v___x_1534_);
if (v___x_1535_ == 0)
{
lean_object* v___x_1536_; lean_object* v___x_1537_; 
lean_inc(v_idx_1529_);
lean_inc(v_typeName_1528_);
lean_dec_ref(v___y_1466_);
v___x_1536_ = l_Lean_Expr_proj___override(v_typeName_1528_, v_idx_1529_, v_a_1532_);
v___x_1537_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1408_, v_post_1410_, v___x_1536_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
return v___x_1537_;
}
else
{
lean_object* v___x_1538_; 
lean_dec(v_a_1532_);
v___x_1538_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1408_, v_post_1410_, v___y_1466_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
return v___x_1538_;
}
}
else
{
lean_dec_ref(v___y_1466_);
lean_dec_ref(v_post_1410_);
lean_dec_ref(v_pre_1408_);
return v___x_1531_;
}
}
default: 
{
lean_object* v___x_1539_; 
v___x_1539_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1408_, v_post_1410_, v___y_1466_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
return v___x_1539_;
}
}
}
}
}
else
{
lean_object* v_a_1551_; lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1558_; 
lean_dec_ref(v_post_1410_);
lean_dec_ref(v_e_1409_);
lean_dec_ref(v_pre_1408_);
v_a_1551_ = lean_ctor_get(v___x_1460_, 0);
v_isSharedCheck_1558_ = !lean_is_exclusive(v___x_1460_);
if (v_isSharedCheck_1558_ == 0)
{
v___x_1553_ = v___x_1460_;
v_isShared_1554_ = v_isSharedCheck_1558_;
goto v_resetjp_1552_;
}
else
{
lean_inc(v_a_1551_);
lean_dec(v___x_1460_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1558_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v___x_1556_; 
if (v_isShared_1554_ == 0)
{
v___x_1556_ = v___x_1553_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v_a_1551_);
v___x_1556_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
return v___x_1556_;
}
}
}
v___jp_1417_:
{
if (v___y_1425_ == 0)
{
lean_object* v___x_1426_; lean_object* v___x_1427_; 
lean_dec_ref(v___y_1423_);
lean_dec_ref(v___y_1420_);
v___x_1426_ = l_Lean_Expr_letE___override(v___y_1424_, v___y_1419_, v___y_1421_, v___y_1418_, v___y_1422_);
v___x_1427_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1408_, v_post_1410_, v___x_1426_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
return v___x_1427_;
}
else
{
size_t v___x_1428_; size_t v___x_1429_; uint8_t v___x_1430_; 
v___x_1428_ = lean_ptr_addr(v___y_1420_);
lean_dec_ref(v___y_1420_);
v___x_1429_ = lean_ptr_addr(v___y_1418_);
v___x_1430_ = lean_usize_dec_eq(v___x_1428_, v___x_1429_);
if (v___x_1430_ == 0)
{
lean_object* v___x_1431_; lean_object* v___x_1432_; 
lean_dec_ref(v___y_1423_);
v___x_1431_ = l_Lean_Expr_letE___override(v___y_1424_, v___y_1419_, v___y_1421_, v___y_1418_, v___y_1422_);
v___x_1432_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1408_, v_post_1410_, v___x_1431_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
return v___x_1432_;
}
else
{
lean_object* v___x_1433_; 
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1421_);
lean_dec_ref(v___y_1419_);
lean_dec_ref(v___y_1418_);
v___x_1433_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1408_, v_post_1410_, v___y_1423_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
return v___x_1433_;
}
}
}
v___jp_1434_:
{
if (v___y_1440_ == 0)
{
lean_object* v___x_1441_; lean_object* v___x_1442_; 
lean_dec_ref(v___y_1439_);
v___x_1441_ = l_Lean_Expr_lam___override(v___y_1438_, v___y_1436_, v___y_1435_, v___y_1437_);
v___x_1442_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1408_, v_post_1410_, v___x_1441_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
return v___x_1442_;
}
else
{
uint8_t v___x_1443_; 
v___x_1443_ = l_Lean_instBEqBinderInfo_beq(v___y_1437_, v___y_1437_);
if (v___x_1443_ == 0)
{
lean_object* v___x_1444_; lean_object* v___x_1445_; 
lean_dec_ref(v___y_1439_);
v___x_1444_ = l_Lean_Expr_lam___override(v___y_1438_, v___y_1436_, v___y_1435_, v___y_1437_);
v___x_1445_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1408_, v_post_1410_, v___x_1444_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
return v___x_1445_;
}
else
{
lean_object* v___x_1446_; 
lean_dec(v___y_1438_);
lean_dec_ref(v___y_1436_);
lean_dec_ref(v___y_1435_);
v___x_1446_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1408_, v_post_1410_, v___y_1439_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
return v___x_1446_;
}
}
}
v___jp_1447_:
{
if (v___y_1453_ == 0)
{
lean_object* v___x_1454_; lean_object* v___x_1455_; 
lean_dec_ref(v___y_1452_);
v___x_1454_ = l_Lean_Expr_forallE___override(v___y_1451_, v___y_1448_, v___y_1450_, v___y_1449_);
v___x_1455_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1408_, v_post_1410_, v___x_1454_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
return v___x_1455_;
}
else
{
uint8_t v___x_1456_; 
v___x_1456_ = l_Lean_instBEqBinderInfo_beq(v___y_1449_, v___y_1449_);
if (v___x_1456_ == 0)
{
lean_object* v___x_1457_; lean_object* v___x_1458_; 
lean_dec_ref(v___y_1452_);
v___x_1457_ = l_Lean_Expr_forallE___override(v___y_1451_, v___y_1448_, v___y_1450_, v___y_1449_);
v___x_1458_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1408_, v_post_1410_, v___x_1457_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
return v___x_1458_;
}
else
{
lean_object* v___x_1459_; 
lean_dec(v___y_1451_);
lean_dec_ref(v___y_1450_);
lean_dec_ref(v___y_1448_);
v___x_1459_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1408_, v_post_1410_, v___y_1452_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
return v___x_1459_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__1___boxed(lean_object* v_pre_1559_, lean_object* v_e_1560_, lean_object* v_post_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_){
_start:
{
lean_object* v_res_1568_; 
v_res_1568_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__1(v_pre_1559_, v_e_1560_, v_post_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_);
lean_dec(v___y_1566_);
lean_dec_ref(v___y_1565_);
lean_dec(v___y_1564_);
lean_dec_ref(v___y_1563_);
lean_dec(v___y_1562_);
return v_res_1568_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(lean_object* v_pre_1569_, lean_object* v_post_1570_, lean_object* v_e_1571_, lean_object* v_a_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_){
_start:
{
lean_object* v___x_1578_; lean_object* v___x_1579_; 
lean_inc(v_a_1572_);
v___x_1578_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1578_, 0, lean_box(0));
lean_closure_set(v___x_1578_, 1, lean_box(0));
lean_closure_set(v___x_1578_, 2, v_a_1572_);
v___x_1579_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__0(lean_box(0), v___x_1578_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_);
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_object* v_a_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1610_; 
v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
v_isSharedCheck_1610_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1582_ = v___x_1579_;
v_isShared_1583_ = v_isSharedCheck_1610_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_a_1580_);
lean_dec(v___x_1579_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1610_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
lean_object* v___x_1584_; 
v___x_1584_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3___redArg(v_a_1580_, v_e_1571_);
lean_dec(v_a_1580_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v___f_1585_; lean_object* v___x_1586_; 
lean_del_object(v___x_1582_);
lean_inc_ref(v_e_1571_);
v___f_1585_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__1___boxed), 9, 3);
lean_closure_set(v___f_1585_, 0, v_pre_1569_);
lean_closure_set(v___f_1585_, 1, v_e_1571_);
lean_closure_set(v___f_1585_, 2, v_post_1570_);
v___x_1586_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5___redArg(v___f_1585_, v_a_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_);
if (lean_obj_tag(v___x_1586_) == 0)
{
lean_object* v_a_1587_; lean_object* v___f_1588_; lean_object* v___x_1589_; 
v_a_1587_ = lean_ctor_get(v___x_1586_, 0);
lean_inc_n(v_a_1587_, 2);
lean_dec_ref(v___x_1586_);
lean_inc(v_a_1572_);
v___f_1588_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1588_, 0, v_a_1572_);
lean_closure_set(v___f_1588_, 1, v_e_1571_);
lean_closure_set(v___f_1588_, 2, v_a_1587_);
v___x_1589_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__0(lean_box(0), v___f_1588_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_);
if (lean_obj_tag(v___x_1589_) == 0)
{
lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1596_; 
v_isSharedCheck_1596_ = !lean_is_exclusive(v___x_1589_);
if (v_isSharedCheck_1596_ == 0)
{
lean_object* v_unused_1597_; 
v_unused_1597_ = lean_ctor_get(v___x_1589_, 0);
lean_dec(v_unused_1597_);
v___x_1591_ = v___x_1589_;
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
else
{
lean_dec(v___x_1589_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v___x_1594_; 
if (v_isShared_1592_ == 0)
{
lean_ctor_set(v___x_1591_, 0, v_a_1587_);
v___x_1594_ = v___x_1591_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v_a_1587_);
v___x_1594_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
return v___x_1594_;
}
}
}
else
{
lean_object* v_a_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1605_; 
lean_dec(v_a_1587_);
v_a_1598_ = lean_ctor_get(v___x_1589_, 0);
v_isSharedCheck_1605_ = !lean_is_exclusive(v___x_1589_);
if (v_isSharedCheck_1605_ == 0)
{
v___x_1600_ = v___x_1589_;
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_a_1598_);
lean_dec(v___x_1589_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v___x_1603_; 
if (v_isShared_1601_ == 0)
{
v___x_1603_ = v___x_1600_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v_a_1598_);
v___x_1603_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
return v___x_1603_;
}
}
}
}
else
{
lean_dec_ref(v_e_1571_);
return v___x_1586_;
}
}
else
{
lean_object* v_val_1606_; lean_object* v___x_1608_; 
lean_dec_ref(v_e_1571_);
lean_dec_ref(v_post_1570_);
lean_dec_ref(v_pre_1569_);
v_val_1606_ = lean_ctor_get(v___x_1584_, 0);
lean_inc(v_val_1606_);
lean_dec_ref(v___x_1584_);
if (v_isShared_1583_ == 0)
{
lean_ctor_set(v___x_1582_, 0, v_val_1606_);
v___x_1608_ = v___x_1582_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_val_1606_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
}
}
else
{
lean_object* v_a_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1618_; 
lean_dec_ref(v_e_1571_);
lean_dec_ref(v_post_1570_);
lean_dec_ref(v_pre_1569_);
v_a_1611_ = lean_ctor_get(v___x_1579_, 0);
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1613_ = v___x_1579_;
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_a_1611_);
lean_dec(v___x_1579_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v___x_1616_; 
if (v_isShared_1614_ == 0)
{
v___x_1616_ = v___x_1613_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v_a_1611_);
v___x_1616_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
return v___x_1616_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(lean_object* v_pre_1619_, lean_object* v_post_1620_, lean_object* v_e_1621_, lean_object* v_a_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_){
_start:
{
lean_object* v___x_1628_; 
lean_inc_ref(v_post_1620_);
lean_inc(v___y_1626_);
lean_inc_ref(v___y_1625_);
lean_inc(v___y_1624_);
lean_inc_ref(v___y_1623_);
lean_inc_ref(v_e_1621_);
v___x_1628_ = lean_apply_6(v_post_1620_, v_e_1621_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, lean_box(0));
if (lean_obj_tag(v___x_1628_) == 0)
{
lean_object* v_a_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1647_; 
v_a_1629_ = lean_ctor_get(v___x_1628_, 0);
v_isSharedCheck_1647_ = !lean_is_exclusive(v___x_1628_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1631_ = v___x_1628_;
v_isShared_1632_ = v_isSharedCheck_1647_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_a_1629_);
lean_dec(v___x_1628_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1647_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
switch(lean_obj_tag(v_a_1629_))
{
case 0:
{
lean_object* v_e_1633_; lean_object* v___x_1635_; 
lean_dec_ref(v_e_1621_);
lean_dec_ref(v_post_1620_);
lean_dec_ref(v_pre_1619_);
v_e_1633_ = lean_ctor_get(v_a_1629_, 0);
lean_inc_ref(v_e_1633_);
lean_dec_ref(v_a_1629_);
if (v_isShared_1632_ == 0)
{
lean_ctor_set(v___x_1631_, 0, v_e_1633_);
v___x_1635_ = v___x_1631_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_e_1633_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
return v___x_1635_;
}
}
case 1:
{
lean_object* v_e_1637_; lean_object* v___x_1638_; 
lean_del_object(v___x_1631_);
lean_dec_ref(v_e_1621_);
v_e_1637_ = lean_ctor_get(v_a_1629_, 0);
lean_inc_ref(v_e_1637_);
lean_dec_ref(v_a_1629_);
v___x_1638_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1619_, v_post_1620_, v_e_1637_, v_a_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_);
return v___x_1638_;
}
default: 
{
lean_object* v_e_x3f_1639_; 
lean_dec_ref(v_post_1620_);
lean_dec_ref(v_pre_1619_);
v_e_x3f_1639_ = lean_ctor_get(v_a_1629_, 0);
lean_inc(v_e_x3f_1639_);
lean_dec_ref(v_a_1629_);
if (lean_obj_tag(v_e_x3f_1639_) == 0)
{
lean_object* v___x_1641_; 
if (v_isShared_1632_ == 0)
{
lean_ctor_set(v___x_1631_, 0, v_e_1621_);
v___x_1641_ = v___x_1631_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v_e_1621_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
}
}
else
{
lean_object* v_val_1643_; lean_object* v___x_1645_; 
lean_dec_ref(v_e_1621_);
v_val_1643_ = lean_ctor_get(v_e_x3f_1639_, 0);
lean_inc(v_val_1643_);
lean_dec_ref(v_e_x3f_1639_);
if (v_isShared_1632_ == 0)
{
lean_ctor_set(v___x_1631_, 0, v_val_1643_);
v___x_1645_ = v___x_1631_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v_val_1643_);
v___x_1645_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
return v___x_1645_;
}
}
}
}
}
}
else
{
lean_object* v_a_1648_; lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1655_; 
lean_dec_ref(v_e_1621_);
lean_dec_ref(v_post_1620_);
lean_dec_ref(v_pre_1619_);
v_a_1648_ = lean_ctor_get(v___x_1628_, 0);
v_isSharedCheck_1655_ = !lean_is_exclusive(v___x_1628_);
if (v_isSharedCheck_1655_ == 0)
{
v___x_1650_ = v___x_1628_;
v_isShared_1651_ = v_isSharedCheck_1655_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_a_1648_);
lean_dec(v___x_1628_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1655_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v___x_1653_; 
if (v_isShared_1651_ == 0)
{
v___x_1653_ = v___x_1650_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v_a_1648_);
v___x_1653_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
return v___x_1653_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_1656_, lean_object* v_post_1657_, lean_object* v_e_1658_, lean_object* v_a_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_){
_start:
{
lean_object* v_res_1665_; 
v_res_1665_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_1656_, v_post_1657_, v_e_1658_, v_a_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_);
lean_dec(v___y_1663_);
lean_dec_ref(v___y_1662_);
lean_dec(v___y_1661_);
lean_dec_ref(v___y_1660_);
lean_dec(v_a_1659_);
return v_res_1665_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_1666_, lean_object* v_post_1667_, lean_object* v_sz_1668_, lean_object* v_i_1669_, lean_object* v_bs_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_){
_start:
{
size_t v_sz_boxed_1677_; size_t v_i_boxed_1678_; lean_object* v_res_1679_; 
v_sz_boxed_1677_ = lean_unbox_usize(v_sz_1668_);
lean_dec(v_sz_1668_);
v_i_boxed_1678_ = lean_unbox_usize(v_i_1669_);
lean_dec(v_i_1669_);
v_res_1679_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__1(v_pre_1666_, v_post_1667_, v_sz_boxed_1677_, v_i_boxed_1678_, v_bs_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_);
lean_dec(v___y_1675_);
lean_dec_ref(v___y_1674_);
lean_dec(v___y_1673_);
lean_dec_ref(v___y_1672_);
lean_dec(v___y_1671_);
return v_res_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__4___boxed(lean_object* v_pre_1680_, lean_object* v_post_1681_, lean_object* v_x_1682_, lean_object* v_x_1683_, lean_object* v_x_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_){
_start:
{
lean_object* v_res_1691_; 
v_res_1691_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__4(v_pre_1680_, v_post_1681_, v_x_1682_, v_x_1683_, v_x_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_);
lean_dec(v___y_1689_);
lean_dec_ref(v___y_1688_);
lean_dec(v___y_1687_);
lean_dec_ref(v___y_1686_);
lean_dec(v___y_1685_);
return v_res_1691_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___boxed(lean_object* v_pre_1692_, lean_object* v_post_1693_, lean_object* v_e_1694_, lean_object* v_a_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_){
_start:
{
lean_object* v_res_1701_; 
v_res_1701_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1692_, v_post_1693_, v_e_1694_, v_a_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_);
lean_dec(v___y_1699_);
lean_dec_ref(v___y_1698_);
lean_dec(v___y_1697_);
lean_dec_ref(v___y_1696_);
lean_dec(v_a_1695_);
return v_res_1701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___lam__0(lean_object* v_00_u03b1_1702_, lean_object* v_x_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_){
_start:
{
lean_object* v___x_1709_; lean_object* v___x_1710_; 
v___x_1709_ = lean_apply_1(v_x_1703_, lean_box(0));
v___x_1710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1710_, 0, v___x_1709_);
return v___x_1710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___lam__0___boxed(lean_object* v_00_u03b1_1711_, lean_object* v_x_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_){
_start:
{
lean_object* v_res_1718_; 
v_res_1718_ = l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___lam__0(v_00_u03b1_1711_, v_x_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
lean_dec(v___y_1714_);
lean_dec_ref(v___y_1713_);
return v_res_1718_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; 
v___x_1719_ = lean_box(0);
v___x_1720_ = lean_unsigned_to_nat(16u);
v___x_1721_ = lean_mk_array(v___x_1720_, v___x_1719_);
return v___x_1721_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; 
v___x_1722_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__0, &l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__0_once, _init_l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__0);
v___x_1723_ = lean_unsigned_to_nat(0u);
v___x_1724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1724_, 0, v___x_1723_);
lean_ctor_set(v___x_1724_, 1, v___x_1722_);
return v___x_1724_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1725_; lean_object* v___x_1726_; 
v___x_1725_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__1, &l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__1_once, _init_l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__1);
v___x_1726_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1726_, 0, lean_box(0));
lean_closure_set(v___x_1726_, 1, lean_box(0));
lean_closure_set(v___x_1726_, 2, v___x_1725_);
return v___x_1726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0(lean_object* v_input_1727_, lean_object* v_pre_1728_, lean_object* v_post_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_){
_start:
{
lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v_a_1737_; lean_object* v___x_1738_; 
v___x_1735_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__2, &l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__2_once, _init_l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__2);
v___x_1736_ = l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___lam__0(lean_box(0), v___x_1735_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
v_a_1737_ = lean_ctor_get(v___x_1736_, 0);
lean_inc(v_a_1737_);
lean_dec_ref(v___x_1736_);
v___x_1738_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_1728_, v_post_1729_, v_input_1727_, v_a_1737_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
if (lean_obj_tag(v___x_1738_) == 0)
{
lean_object* v_a_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1748_; 
v_a_1739_ = lean_ctor_get(v___x_1738_, 0);
lean_inc(v_a_1739_);
lean_dec_ref(v___x_1738_);
v___x_1740_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1740_, 0, lean_box(0));
lean_closure_set(v___x_1740_, 1, lean_box(0));
lean_closure_set(v___x_1740_, 2, v_a_1737_);
v___x_1741_ = l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___lam__0(lean_box(0), v___x_1740_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
v_isSharedCheck_1748_ = !lean_is_exclusive(v___x_1741_);
if (v_isSharedCheck_1748_ == 0)
{
lean_object* v_unused_1749_; 
v_unused_1749_ = lean_ctor_get(v___x_1741_, 0);
lean_dec(v_unused_1749_);
v___x_1743_ = v___x_1741_;
v_isShared_1744_ = v_isSharedCheck_1748_;
goto v_resetjp_1742_;
}
else
{
lean_dec(v___x_1741_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1748_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
lean_object* v___x_1746_; 
if (v_isShared_1744_ == 0)
{
lean_ctor_set(v___x_1743_, 0, v_a_1739_);
v___x_1746_ = v___x_1743_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v_a_1739_);
v___x_1746_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
return v___x_1746_;
}
}
}
else
{
lean_dec(v_a_1737_);
return v___x_1738_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___boxed(lean_object* v_input_1750_, lean_object* v_pre_1751_, lean_object* v_post_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_){
_start:
{
lean_object* v_res_1758_; 
v_res_1758_ = l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0(v_input_1750_, v_pre_1751_, v_post_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_);
lean_dec(v___y_1756_);
lean_dec_ref(v___y_1755_);
lean_dec(v___y_1754_);
lean_dec_ref(v___y_1753_);
return v_res_1758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_reduceProjs(lean_object* v_e_1761_, lean_object* v_a_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_){
_start:
{
lean_object* v___f_1767_; lean_object* v___f_1768_; lean_object* v___x_1769_; 
v___f_1767_ = ((lean_object*)(l_Lean_Meta_PProdN_reduceProjs___closed__0));
v___f_1768_ = ((lean_object*)(l_Lean_Meta_PProdN_reduceProjs___closed__1));
v___x_1769_ = l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0(v_e_1761_, v___f_1767_, v___f_1768_, v_a_1762_, v_a_1763_, v_a_1764_, v_a_1765_);
return v___x_1769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_PProdN_reduceProjs___boxed(lean_object* v_e_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_){
_start:
{
lean_object* v_res_1776_; 
v_res_1776_ = l_Lean_Meta_PProdN_reduceProjs(v_e_1770_, v_a_1771_, v_a_1772_, v_a_1773_, v_a_1774_);
lean_dec(v_a_1774_);
lean_dec_ref(v_a_1773_);
lean_dec(v_a_1772_);
lean_dec_ref(v_a_1771_);
return v_res_1776_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_1777_, lean_object* v_m_1778_, lean_object* v_a_1779_){
_start:
{
lean_object* v___x_1780_; 
v___x_1780_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3___redArg(v_m_1778_, v_a_1779_);
return v___x_1780_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_1781_, lean_object* v_m_1782_, lean_object* v_a_1783_){
_start:
{
lean_object* v_res_1784_; 
v_res_1784_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3(v_00_u03b2_1781_, v_m_1782_, v_a_1783_);
lean_dec_ref(v_a_1783_);
lean_dec_ref(v_m_1782_);
return v_res_1784_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_1785_, lean_object* v_ref_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_){
_start:
{
lean_object* v___x_1790_; 
v___x_1790_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_1786_);
return v___x_1790_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1791_, lean_object* v_ref_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_){
_start:
{
lean_object* v_res_1796_; 
v_res_1796_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_1791_, v_ref_1792_, v___y_1793_, v___y_1794_);
lean_dec(v___y_1794_);
lean_dec_ref(v___y_1793_);
return v_res_1796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5(lean_object* v_00_u03b1_1797_, lean_object* v_x_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_){
_start:
{
lean_object* v___x_1805_; 
v___x_1805_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5___redArg(v_x_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_);
return v___x_1805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b1_1806_, lean_object* v_x_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_){
_start:
{
lean_object* v_res_1814_; 
v_res_1814_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5(v_00_u03b1_1806_, v_x_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
lean_dec(v___y_1810_);
lean_dec_ref(v___y_1809_);
lean_dec(v___y_1808_);
return v_res_1814_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6(lean_object* v_00_u03b2_1815_, lean_object* v_m_1816_, lean_object* v_a_1817_, lean_object* v_b_1818_){
_start:
{
lean_object* v___x_1819_; 
v___x_1819_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6___redArg(v_m_1816_, v_a_1817_, v_b_1818_);
return v___x_1819_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b2_1820_, lean_object* v_a_1821_, lean_object* v_x_1822_){
_start:
{
lean_object* v___x_1823_; 
v___x_1823_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3_spec__4___redArg(v_a_1821_, v_x_1822_);
return v___x_1823_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3_spec__4___boxed(lean_object* v_00_u03b2_1824_, lean_object* v_a_1825_, lean_object* v_x_1826_){
_start:
{
lean_object* v_res_1827_; 
v_res_1827_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3_spec__4(v_00_u03b2_1824_, v_a_1825_, v_x_1826_);
lean_dec(v_x_1826_);
lean_dec_ref(v_a_1825_);
return v_res_1827_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__9(lean_object* v_00_u03b2_1828_, lean_object* v_a_1829_, lean_object* v_x_1830_){
_start:
{
uint8_t v___x_1831_; 
v___x_1831_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__9___redArg(v_a_1829_, v_x_1830_);
return v___x_1831_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__9___boxed(lean_object* v_00_u03b2_1832_, lean_object* v_a_1833_, lean_object* v_x_1834_){
_start:
{
uint8_t v_res_1835_; lean_object* v_r_1836_; 
v_res_1835_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__9(v_00_u03b2_1832_, v_a_1833_, v_x_1834_);
lean_dec(v_x_1834_);
lean_dec_ref(v_a_1833_);
v_r_1836_ = lean_box(v_res_1835_);
return v_r_1836_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__10(lean_object* v_00_u03b2_1837_, lean_object* v_data_1838_){
_start:
{
lean_object* v___x_1839_; 
v___x_1839_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__10___redArg(v_data_1838_);
return v___x_1839_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11(lean_object* v_00_u03b2_1840_, lean_object* v_a_1841_, lean_object* v_b_1842_, lean_object* v_x_1843_){
_start:
{
lean_object* v___x_1844_; 
v___x_1844_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11___redArg(v_a_1841_, v_b_1842_, v_x_1843_);
return v___x_1844_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__10_spec__11(lean_object* v_00_u03b2_1845_, lean_object* v_i_1846_, lean_object* v_source_1847_, lean_object* v_target_1848_){
_start:
{
lean_object* v___x_1849_; 
v___x_1849_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__10_spec__11___redArg(v_i_1846_, v_source_1847_, v_target_1848_);
return v___x_1849_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12(lean_object* v_00_u03b2_1850_, lean_object* v_x_1851_, lean_object* v_x_1852_){
_start:
{
lean_object* v___x_1853_; 
v___x_1853_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12___redArg(v_x_1851_, v_x_1852_);
return v___x_1853_;
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
