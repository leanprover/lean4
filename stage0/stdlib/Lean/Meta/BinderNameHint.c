// Lean compiler output
// Module: Lean.Meta.BinderNameHint
// Imports: public import Lean.Meta.Basic
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
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_ExprStructEq_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* l_Array_instInhabited(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ExprStructEq_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_ExprStructEq_hash___boxed(lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadCacheT_instMonad___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
lean_object* l_Lean_Core_instInhabitedCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_hasBinderNameHint___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "binderNameHint"};
static const lean_object* l_Lean_Expr_hasBinderNameHint___lam__0___closed__0 = (const lean_object*)&l_Lean_Expr_hasBinderNameHint___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Expr_hasBinderNameHint___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_hasBinderNameHint___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(51, 69, 86, 160, 190, 96, 121, 153)}};
static const lean_object* l_Lean_Expr_hasBinderNameHint___lam__0___closed__1 = (const lean_object*)&l_Lean_Expr_hasBinderNameHint___lam__0___closed__1_value;
LEAN_EXPORT uint8_t l_Lean_Expr_hasBinderNameHint___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasBinderNameHint___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Expr_hasBinderNameHint___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_hasBinderNameHint___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Expr_hasBinderNameHint___closed__0 = (const lean_object*)&l_Lean_Expr_hasBinderNameHint___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Expr_hasBinderNameHint(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasBinderNameHint___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_BinderNameHint_0__Lean_enterScope(lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_exitScope_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_exitScope_spec__0___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_exitScope_spec__0(lean_object*);
static const lean_string_object l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.Meta.BinderNameHint"};
static const lean_object* l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope___closed__0 = (const lean_object*)&l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope___closed__0_value;
static const lean_string_object l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = "_private.Lean.Meta.BinderNameHint.0.Lean.exitScope"};
static const lean_object* l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope___closed__1 = (const lean_object*)&l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope___closed__1_value;
static const lean_string_object l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "assertion violation: xs.size > 0\n    "};
static const lean_object* l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope___closed__2 = (const lean_object*)&l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_rememberName_spec__0(lean_object*);
static const lean_string_object l___private_Lean_Meta_BinderNameHint_0__Lean_rememberName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "_private.Lean.Meta.BinderNameHint.0.Lean.rememberName"};
static const lean_object* l___private_Lean_Meta_BinderNameHint_0__Lean_rememberName___closed__0 = (const lean_object*)&l___private_Lean_Meta_BinderNameHint_0__Lean_rememberName___closed__0_value;
static const lean_string_object l___private_Lean_Meta_BinderNameHint_0__Lean_rememberName___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "assertion violation: xs.size > bidx\n    "};
static const lean_object* l___private_Lean_Meta_BinderNameHint_0__Lean_rememberName___closed__1 = (const lean_object*)&l___private_Lean_Meta_BinderNameHint_0__Lean_rememberName___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_BinderNameHint_0__Lean_rememberName___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_BinderNameHint_0__Lean_rememberName___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_BinderNameHint_0__Lean_rememberName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_BinderNameHint_0__Lean_rememberName___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_makeFresh_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instInhabitedCoreM___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_makeFresh_spec__0___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_makeFresh_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_makeFresh_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_makeFresh_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_BinderNameHint_0__Lean_makeFresh___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = "_private.Lean.Meta.BinderNameHint.0.Lean.makeFresh"};
static const lean_object* l___private_Lean_Meta_BinderNameHint_0__Lean_makeFresh___closed__0 = (const lean_object*)&l___private_Lean_Meta_BinderNameHint_0__Lean_makeFresh___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_BinderNameHint_0__Lean_makeFresh___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_BinderNameHint_0__Lean_makeFresh___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_BinderNameHint_0__Lean_makeFresh(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_BinderNameHint_0__Lean_makeFresh___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__3___closed__0;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__3___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__3___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__3___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__3___closed__2_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ExprStructEq_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__3___closed__3 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__3___closed__3_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ExprStructEq_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__3___closed__4 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__3___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1___redArg___boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 71, .m_capacity = 71, .m_length = 70, .m_data = "_private.Lean.Meta.BinderNameHint.0.Lean.Expr.resolveBinderNameHint.go"};
static const lean_object* l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___closed__0_value;
static const lean_string_object l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "assertion violation: xs.size > bidx\n          "};
static const lean_object* l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___closed__1 = (const lean_object*)&l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Expr_resolveBinderNameHint___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_resolveBinderNameHint___closed__0;
static lean_once_cell_t l_Lean_Expr_resolveBinderNameHint___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_resolveBinderNameHint___closed__1;
static lean_once_cell_t l_Lean_Expr_resolveBinderNameHint___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_resolveBinderNameHint___closed__2;
static const lean_array_object l_Lean_Expr_resolveBinderNameHint___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Expr_resolveBinderNameHint___closed__3 = (const lean_object*)&l_Lean_Expr_resolveBinderNameHint___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Expr_resolveBinderNameHint(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_resolveBinderNameHint___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_hasBinderNameHint___lam__0(lean_object* v_e_4_){
_start:
{
lean_object* v___x_5_; uint8_t v___x_6_; 
v___x_5_ = ((lean_object*)(l_Lean_Expr_hasBinderNameHint___lam__0___closed__1));
v___x_6_ = l_Lean_Expr_isConstOf(v_e_4_, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasBinderNameHint___lam__0___boxed(lean_object* v_e_7_){
_start:
{
uint8_t v_res_8_; lean_object* v_r_9_; 
v_res_8_ = l_Lean_Expr_hasBinderNameHint___lam__0(v_e_7_);
lean_dec_ref(v_e_7_);
v_r_9_ = lean_box(v_res_8_);
return v_r_9_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasBinderNameHint(lean_object* v_e_11_){
_start:
{
lean_object* v___f_12_; lean_object* v___x_13_; 
v___f_12_ = ((lean_object*)(l_Lean_Expr_hasBinderNameHint___closed__0));
v___x_13_ = lean_find_expr(v___f_12_, v_e_11_);
if (lean_obj_tag(v___x_13_) == 0)
{
uint8_t v___x_14_; 
v___x_14_ = 0;
return v___x_14_;
}
else
{
uint8_t v___x_15_; 
lean_dec_ref_known(v___x_13_, 1);
v___x_15_ = 1;
return v___x_15_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasBinderNameHint___boxed(lean_object* v_e_16_){
_start:
{
uint8_t v_res_17_; lean_object* v_r_18_; 
v_res_17_ = l_Lean_Expr_hasBinderNameHint(v_e_16_);
lean_dec_ref(v_e_16_);
v_r_18_ = lean_box(v_res_17_);
return v_r_18_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_BinderNameHint_0__Lean_enterScope(lean_object* v_name_19_, lean_object* v_xs_20_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = lean_array_push(v_xs_20_, v_name_19_);
return v___x_21_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_exitScope_spec__0___closed__0(void){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = l_Array_instInhabited(lean_box(0));
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_exitScope_spec__0(lean_object* v_msg_23_){
_start:
{
lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_24_ = lean_box(0);
v___x_25_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_exitScope_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_exitScope_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_exitScope_spec__0___closed__0);
v___x_26_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_26_, 0, v___x_24_);
lean_ctor_set(v___x_26_, 1, v___x_25_);
v___x_27_ = lean_panic_fn_borrowed(v___x_26_, v_msg_23_);
lean_dec_ref_known(v___x_26_, 2);
return v___x_27_;
}
}
static lean_object* _init_l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope___closed__3(void){
_start:
{
lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_31_ = ((lean_object*)(l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope___closed__2));
v___x_32_ = lean_unsigned_to_nat(4u);
v___x_33_ = lean_unsigned_to_nat(26u);
v___x_34_ = ((lean_object*)(l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope___closed__1));
v___x_35_ = ((lean_object*)(l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope___closed__0));
v___x_36_ = l_mkPanicMessageWithDecl(v___x_35_, v___x_34_, v___x_33_, v___x_32_, v___x_31_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope(lean_object* v_xs_37_){
_start:
{
lean_object* v___x_38_; lean_object* v___x_39_; uint8_t v___x_40_; 
v___x_38_ = lean_unsigned_to_nat(0u);
v___x_39_ = lean_array_get_size(v_xs_37_);
v___x_40_ = lean_nat_dec_lt(v___x_38_, v___x_39_);
if (v___x_40_ == 0)
{
lean_object* v___x_41_; lean_object* v___x_42_; 
lean_dec_ref(v_xs_37_);
v___x_41_ = lean_obj_once(&l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope___closed__3, &l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope___closed__3_once, _init_l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope___closed__3);
v___x_42_ = l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_exitScope_spec__0(v___x_41_);
return v___x_42_;
}
else
{
lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_43_ = lean_box(0);
v___x_44_ = lean_unsigned_to_nat(1u);
v___x_45_ = lean_nat_sub(v___x_39_, v___x_44_);
v___x_46_ = lean_array_get(v___x_43_, v_xs_37_, v___x_45_);
lean_dec(v___x_45_);
v___x_47_ = lean_array_pop(v_xs_37_);
v___x_48_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_48_, 0, v___x_46_);
lean_ctor_set(v___x_48_, 1, v___x_47_);
return v___x_48_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_rememberName_spec__0(lean_object* v_msg_49_){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_50_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_exitScope_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_exitScope_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_exitScope_spec__0___closed__0);
v___x_51_ = lean_panic_fn_borrowed(v___x_50_, v_msg_49_);
return v___x_51_;
}
}
static lean_object* _init_l___private_Lean_Meta_BinderNameHint_0__Lean_rememberName___closed__2(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_54_ = ((lean_object*)(l___private_Lean_Meta_BinderNameHint_0__Lean_rememberName___closed__1));
v___x_55_ = lean_unsigned_to_nat(4u);
v___x_56_ = lean_unsigned_to_nat(30u);
v___x_57_ = ((lean_object*)(l___private_Lean_Meta_BinderNameHint_0__Lean_rememberName___closed__0));
v___x_58_ = ((lean_object*)(l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope___closed__0));
v___x_59_ = l_mkPanicMessageWithDecl(v___x_58_, v___x_57_, v___x_56_, v___x_55_, v___x_54_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_BinderNameHint_0__Lean_rememberName(lean_object* v_bidx_60_, lean_object* v_name_61_, lean_object* v_xs_62_){
_start:
{
lean_object* v___x_63_; uint8_t v___x_64_; 
v___x_63_ = lean_array_get_size(v_xs_62_);
v___x_64_ = lean_nat_dec_lt(v_bidx_60_, v___x_63_);
if (v___x_64_ == 0)
{
lean_object* v___x_65_; lean_object* v___x_66_; 
lean_dec_ref(v_xs_62_);
lean_dec(v_name_61_);
v___x_65_ = lean_obj_once(&l___private_Lean_Meta_BinderNameHint_0__Lean_rememberName___closed__2, &l___private_Lean_Meta_BinderNameHint_0__Lean_rememberName___closed__2_once, _init_l___private_Lean_Meta_BinderNameHint_0__Lean_rememberName___closed__2);
v___x_66_ = l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_rememberName_spec__0(v___x_65_);
return v___x_66_;
}
else
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_67_ = lean_nat_sub(v___x_63_, v_bidx_60_);
v___x_68_ = lean_unsigned_to_nat(1u);
v___x_69_ = lean_nat_sub(v___x_67_, v___x_68_);
lean_dec(v___x_67_);
v___x_70_ = lean_array_set(v_xs_62_, v___x_69_, v_name_61_);
lean_dec(v___x_69_);
return v___x_70_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_BinderNameHint_0__Lean_rememberName___boxed(lean_object* v_bidx_71_, lean_object* v_name_72_, lean_object* v_xs_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l___private_Lean_Meta_BinderNameHint_0__Lean_rememberName(v_bidx_71_, v_name_72_, v_xs_73_);
lean_dec(v_bidx_71_);
return v_res_74_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_makeFresh_spec__0(lean_object* v_msg_76_, lean_object* v___y_77_, lean_object* v___y_78_){
_start:
{
lean_object* v___f_80_; lean_object* v___x_289__overap_81_; lean_object* v___x_82_; 
v___f_80_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_makeFresh_spec__0___closed__0));
v___x_289__overap_81_ = lean_panic_fn_borrowed(v___f_80_, v_msg_76_);
lean_inc(v___y_78_);
lean_inc_ref(v___y_77_);
v___x_82_ = lean_apply_3(v___x_289__overap_81_, v___y_77_, v___y_78_, lean_box(0));
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_makeFresh_spec__0___boxed(lean_object* v_msg_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_makeFresh_spec__0(v_msg_83_, v___y_84_, v___y_85_);
lean_dec(v___y_85_);
lean_dec_ref(v___y_84_);
return v_res_87_;
}
}
static lean_object* _init_l___private_Lean_Meta_BinderNameHint_0__Lean_makeFresh___closed__1(void){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_89_ = ((lean_object*)(l___private_Lean_Meta_BinderNameHint_0__Lean_rememberName___closed__1));
v___x_90_ = lean_unsigned_to_nat(4u);
v___x_91_ = lean_unsigned_to_nat(34u);
v___x_92_ = ((lean_object*)(l___private_Lean_Meta_BinderNameHint_0__Lean_makeFresh___closed__0));
v___x_93_ = ((lean_object*)(l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope___closed__0));
v___x_94_ = l_mkPanicMessageWithDecl(v___x_93_, v___x_92_, v___x_91_, v___x_90_, v___x_89_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_BinderNameHint_0__Lean_makeFresh(lean_object* v_bidx_95_, lean_object* v_xs_96_, lean_object* v_a_97_, lean_object* v_a_98_){
_start:
{
lean_object* v___x_100_; uint8_t v___x_101_; 
v___x_100_ = lean_array_get_size(v_xs_96_);
v___x_101_ = lean_nat_dec_lt(v_bidx_95_, v___x_100_);
if (v___x_101_ == 0)
{
lean_object* v___x_102_; lean_object* v___x_103_; 
lean_dec_ref(v_xs_96_);
v___x_102_ = lean_obj_once(&l___private_Lean_Meta_BinderNameHint_0__Lean_makeFresh___closed__1, &l___private_Lean_Meta_BinderNameHint_0__Lean_makeFresh___closed__1_once, _init_l___private_Lean_Meta_BinderNameHint_0__Lean_makeFresh___closed__1);
v___x_103_ = l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_makeFresh_spec__0(v___x_102_, v_a_97_, v_a_98_);
return v___x_103_;
}
else
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v_name_108_; lean_object* v___x_109_; 
v___x_104_ = lean_box(0);
v___x_105_ = lean_nat_sub(v___x_100_, v_bidx_95_);
v___x_106_ = lean_unsigned_to_nat(1u);
v___x_107_ = lean_nat_sub(v___x_105_, v___x_106_);
lean_dec(v___x_105_);
v_name_108_ = lean_array_get_borrowed(v___x_104_, v_xs_96_, v___x_107_);
lean_inc(v_name_108_);
v___x_109_ = l_Lean_Core_mkFreshUserName(v_name_108_, v_a_97_, v_a_98_);
if (lean_obj_tag(v___x_109_) == 0)
{
lean_object* v_a_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_118_; 
v_a_110_ = lean_ctor_get(v___x_109_, 0);
v_isSharedCheck_118_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_118_ == 0)
{
v___x_112_ = v___x_109_;
v_isShared_113_ = v_isSharedCheck_118_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_a_110_);
lean_dec(v___x_109_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_118_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
lean_object* v___x_114_; lean_object* v___x_116_; 
v___x_114_ = lean_array_set(v_xs_96_, v___x_107_, v_a_110_);
lean_dec(v___x_107_);
if (v_isShared_113_ == 0)
{
lean_ctor_set(v___x_112_, 0, v___x_114_);
v___x_116_ = v___x_112_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v___x_114_);
v___x_116_ = v_reuseFailAlloc_117_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
return v___x_116_;
}
}
}
else
{
lean_object* v_a_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_126_; 
lean_dec(v___x_107_);
lean_dec_ref(v_xs_96_);
v_a_119_ = lean_ctor_get(v___x_109_, 0);
v_isSharedCheck_126_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_126_ == 0)
{
v___x_121_ = v___x_109_;
v_isShared_122_ = v_isSharedCheck_126_;
goto v_resetjp_120_;
}
else
{
lean_inc(v_a_119_);
lean_dec(v___x_109_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_126_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
lean_object* v___x_124_; 
if (v_isShared_122_ == 0)
{
v___x_124_ = v___x_121_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v_a_119_);
v___x_124_ = v_reuseFailAlloc_125_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
return v___x_124_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_BinderNameHint_0__Lean_makeFresh___boxed(lean_object* v_bidx_127_, lean_object* v_xs_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l___private_Lean_Meta_BinderNameHint_0__Lean_makeFresh(v_bidx_127_, v_xs_128_, v_a_129_, v_a_130_);
lean_dec(v_a_130_);
lean_dec_ref(v_a_129_);
lean_dec(v_bidx_127_);
return v_res_132_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__3___closed__0(void){
_start:
{
lean_object* v___x_133_; 
v___x_133_ = l_instMonadEIO(lean_box(0));
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__3(lean_object* v_msg_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v_toApplicative_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_191_; 
v___x_144_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__3___closed__0, &l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__3___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__3___closed__0);
v___x_145_ = l_StateRefT_x27_instMonad___redArg(v___x_144_);
v_toApplicative_146_ = lean_ctor_get(v___x_145_, 0);
v_isSharedCheck_191_ = !lean_is_exclusive(v___x_145_);
if (v_isSharedCheck_191_ == 0)
{
lean_object* v_unused_192_; 
v_unused_192_ = lean_ctor_get(v___x_145_, 1);
lean_dec(v_unused_192_);
v___x_148_ = v___x_145_;
v_isShared_149_ = v_isSharedCheck_191_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_toApplicative_146_);
lean_dec(v___x_145_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_191_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v_toFunctor_150_; lean_object* v_toSeq_151_; lean_object* v_toSeqLeft_152_; lean_object* v_toSeqRight_153_; lean_object* v___x_155_; uint8_t v_isShared_156_; uint8_t v_isSharedCheck_189_; 
v_toFunctor_150_ = lean_ctor_get(v_toApplicative_146_, 0);
v_toSeq_151_ = lean_ctor_get(v_toApplicative_146_, 2);
v_toSeqLeft_152_ = lean_ctor_get(v_toApplicative_146_, 3);
v_toSeqRight_153_ = lean_ctor_get(v_toApplicative_146_, 4);
v_isSharedCheck_189_ = !lean_is_exclusive(v_toApplicative_146_);
if (v_isSharedCheck_189_ == 0)
{
lean_object* v_unused_190_; 
v_unused_190_ = lean_ctor_get(v_toApplicative_146_, 1);
lean_dec(v_unused_190_);
v___x_155_ = v_toApplicative_146_;
v_isShared_156_ = v_isSharedCheck_189_;
goto v_resetjp_154_;
}
else
{
lean_inc(v_toSeqRight_153_);
lean_inc(v_toSeqLeft_152_);
lean_inc(v_toSeq_151_);
lean_inc(v_toFunctor_150_);
lean_dec(v_toApplicative_146_);
v___x_155_ = lean_box(0);
v_isShared_156_ = v_isSharedCheck_189_;
goto v_resetjp_154_;
}
v_resetjp_154_:
{
lean_object* v___f_157_; lean_object* v___f_158_; lean_object* v___f_159_; lean_object* v___f_160_; lean_object* v___x_161_; lean_object* v___f_162_; lean_object* v___f_163_; lean_object* v___f_164_; lean_object* v___x_166_; 
v___f_157_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__3___closed__1));
v___f_158_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__3___closed__2));
lean_inc_ref(v_toFunctor_150_);
v___f_159_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_159_, 0, v_toFunctor_150_);
v___f_160_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_160_, 0, v_toFunctor_150_);
v___x_161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_161_, 0, v___f_159_);
lean_ctor_set(v___x_161_, 1, v___f_160_);
v___f_162_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_162_, 0, v_toSeqRight_153_);
v___f_163_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_163_, 0, v_toSeqLeft_152_);
v___f_164_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_164_, 0, v_toSeq_151_);
if (v_isShared_156_ == 0)
{
lean_ctor_set(v___x_155_, 4, v___f_162_);
lean_ctor_set(v___x_155_, 3, v___f_163_);
lean_ctor_set(v___x_155_, 2, v___f_164_);
lean_ctor_set(v___x_155_, 1, v___f_157_);
lean_ctor_set(v___x_155_, 0, v___x_161_);
v___x_166_ = v___x_155_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v___x_161_);
lean_ctor_set(v_reuseFailAlloc_188_, 1, v___f_157_);
lean_ctor_set(v_reuseFailAlloc_188_, 2, v___f_164_);
lean_ctor_set(v_reuseFailAlloc_188_, 3, v___f_163_);
lean_ctor_set(v_reuseFailAlloc_188_, 4, v___f_162_);
v___x_166_ = v_reuseFailAlloc_188_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
lean_object* v___x_168_; 
if (v_isShared_149_ == 0)
{
lean_ctor_set(v___x_148_, 1, v___f_158_);
lean_ctor_set(v___x_148_, 0, v___x_166_);
v___x_168_ = v___x_148_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v___x_166_);
lean_ctor_set(v_reuseFailAlloc_187_, 1, v___f_158_);
v___x_168_ = v_reuseFailAlloc_187_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___f_172_; lean_object* v___f_173_; lean_object* v___f_174_; lean_object* v___f_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_16771__overap_185_; lean_object* v___x_186_; 
v___x_169_ = lean_box(0);
v___x_170_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__3___closed__3));
v___x_171_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__3___closed__4));
lean_inc_ref_n(v___x_168_, 6);
v___f_172_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_172_, 0, v___x_168_);
v___f_173_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_173_, 0, v___x_168_);
v___f_174_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_174_, 0, v___x_168_);
v___f_175_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_175_, 0, v___x_168_);
v___x_176_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_176_, 0, lean_box(0));
lean_closure_set(v___x_176_, 1, lean_box(0));
lean_closure_set(v___x_176_, 2, v___x_168_);
v___x_177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_177_, 0, v___x_176_);
lean_ctor_set(v___x_177_, 1, v___f_172_);
v___x_178_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_178_, 0, lean_box(0));
lean_closure_set(v___x_178_, 1, lean_box(0));
lean_closure_set(v___x_178_, 2, v___x_168_);
v___x_179_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_179_, 0, v___x_177_);
lean_ctor_set(v___x_179_, 1, v___x_178_);
lean_ctor_set(v___x_179_, 2, v___f_173_);
lean_ctor_set(v___x_179_, 3, v___f_174_);
lean_ctor_set(v___x_179_, 4, v___f_175_);
v___x_180_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_180_, 0, lean_box(0));
lean_closure_set(v___x_180_, 1, lean_box(0));
lean_closure_set(v___x_180_, 2, v___x_168_);
v___x_181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_181_, 0, v___x_179_);
lean_ctor_set(v___x_181_, 1, v___x_180_);
v___x_182_ = l_Lean_MonadCacheT_instMonad___redArg(v___x_169_, v___x_170_, v___x_171_, v___x_181_);
v___x_183_ = l_Lean_instInhabitedExpr;
v___x_184_ = l_instInhabitedOfMonad___redArg(v___x_182_, v___x_183_);
v___x_16771__overap_185_ = lean_panic_fn_borrowed(v___x_184_, v_msg_138_);
lean_dec(v___x_184_);
lean_inc(v___y_142_);
lean_inc_ref(v___y_141_);
lean_inc(v___y_139_);
v___x_186_ = lean_apply_5(v___x_16771__overap_185_, v___y_139_, v___y_140_, v___y_141_, v___y_142_, lean_box(0));
return v___x_186_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__3___boxed(lean_object* v_msg_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__3(v_msg_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_);
lean_dec(v___y_197_);
lean_dec_ref(v___y_196_);
lean_dec(v___y_194_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___lam__0(lean_object* v_fst_200_, lean_object* v_____r_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_207_, 0, v_fst_200_);
lean_ctor_set(v___x_207_, 1, v___y_203_);
v___x_208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_208_, 0, v___x_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___lam__0___boxed(lean_object* v_fst_209_, lean_object* v_____r_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___lam__0(v_fst_209_, v_____r_210_, v___y_211_, v___y_212_, v___y_213_, v___y_214_);
lean_dec(v___y_214_);
lean_dec_ref(v___y_213_);
lean_dec(v___y_211_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___lam__1(lean_object* v___f_217_, lean_object* v_bidx_218_, lean_object* v_n_219_, lean_object* v_binderType_220_, lean_object* v_body_221_, uint8_t v_binderInfo_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_228_ = lean_box(0);
v___x_229_ = l___private_Lean_Meta_BinderNameHint_0__Lean_rememberName(v_bidx_218_, v_n_219_, v___y_224_);
lean_inc(v___y_226_);
lean_inc_ref(v___y_225_);
lean_inc(v___y_223_);
v___x_230_ = lean_apply_6(v___f_217_, v___x_228_, v___y_223_, v___x_229_, v___y_225_, v___y_226_, lean_box(0));
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___lam__1___boxed(lean_object* v___f_231_, lean_object* v_bidx_232_, lean_object* v_n_233_, lean_object* v_binderType_234_, lean_object* v_body_235_, lean_object* v_binderInfo_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_){
_start:
{
uint8_t v_binderInfo_17406__boxed_242_; lean_object* v_res_243_; 
v_binderInfo_17406__boxed_242_ = lean_unbox(v_binderInfo_236_);
v_res_243_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___lam__1(v___f_231_, v_bidx_232_, v_n_233_, v_binderType_234_, v_body_235_, v_binderInfo_17406__boxed_242_, v___y_237_, v___y_238_, v___y_239_, v___y_240_);
lean_dec(v___y_240_);
lean_dec_ref(v___y_239_);
lean_dec(v___y_237_);
lean_dec_ref(v_body_235_);
lean_dec_ref(v_binderType_234_);
lean_dec(v_bidx_232_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__0___redArg(lean_object* v_m_244_, lean_object* v_query_245_, lean_object* v_x_246_, lean_object* v_x_247_, lean_object* v_x_248_){
_start:
{
lean_object* v_zero_249_; uint8_t v_isZero_250_; 
v_zero_249_ = lean_unsigned_to_nat(0u);
v_isZero_250_ = lean_nat_dec_eq(v_x_247_, v_zero_249_);
if (v_isZero_250_ == 1)
{
lean_dec(v_x_248_);
lean_dec(v_x_247_);
if (lean_obj_tag(v_x_246_) == 0)
{
lean_object* v___x_251_; 
v___x_251_ = lean_box(2);
return v___x_251_;
}
else
{
lean_object* v_val_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_259_; 
v_val_252_ = lean_ctor_get(v_x_246_, 0);
v_isSharedCheck_259_ = !lean_is_exclusive(v_x_246_);
if (v_isSharedCheck_259_ == 0)
{
v___x_254_ = v_x_246_;
v_isShared_255_ = v_isSharedCheck_259_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_val_252_);
lean_dec(v_x_246_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_259_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v___x_257_; 
if (v_isShared_255_ == 0)
{
v___x_257_ = v___x_254_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v_val_252_);
v___x_257_ = v_reuseFailAlloc_258_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
return v___x_257_;
}
}
}
}
else
{
lean_object* v_keyArray_260_; lean_object* v_valueArray_261_; lean_object* v___x_262_; uint8_t v_isSome_263_; 
v_keyArray_260_ = lean_ctor_get(v_m_244_, 1);
v_valueArray_261_ = lean_ctor_get(v_m_244_, 2);
v___x_262_ = lean_array_fget_borrowed(v_keyArray_260_, v_x_248_);
v_isSome_263_ = lean_noption_is_some(v___x_262_);
if (v_isSome_263_ == 0)
{
lean_dec(v_x_247_);
if (lean_obj_tag(v_x_246_) == 0)
{
lean_object* v___x_264_; 
v___x_264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_264_, 0, v_x_248_);
return v___x_264_;
}
else
{
lean_object* v_val_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_272_; 
lean_dec(v_x_248_);
v_val_265_ = lean_ctor_get(v_x_246_, 0);
v_isSharedCheck_272_ = !lean_is_exclusive(v_x_246_);
if (v_isSharedCheck_272_ == 0)
{
v___x_267_ = v_x_246_;
v_isShared_268_ = v_isSharedCheck_272_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_val_265_);
lean_dec(v_x_246_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_272_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_270_; 
if (v_isShared_268_ == 0)
{
v___x_270_ = v___x_267_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v_val_265_);
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
lean_object* v_one_273_; lean_object* v_n_274_; lean_object* v___y_276_; 
v_one_273_ = lean_unsigned_to_nat(1u);
v_n_274_ = lean_nat_sub(v_x_247_, v_one_273_);
lean_dec(v_x_247_);
if (v_isSome_263_ == 0)
{
goto v___jp_282_;
}
else
{
lean_object* v___x_284_; uint8_t v_isSome_285_; 
v___x_284_ = lean_array_fget_borrowed(v_valueArray_261_, v_x_248_);
v_isSome_285_ = lean_noption_is_some(v___x_284_);
if (v_isSome_285_ == 0)
{
goto v___jp_282_;
}
else
{
lean_object* v_val_286_; uint8_t v___x_287_; 
lean_inc(v___x_262_);
v_val_286_ = lean_noption_get(v___x_262_);
v___x_287_ = l_Lean_ExprStructEq_beq(v_val_286_, v_query_245_);
if (v___x_287_ == 0)
{
lean_object* v___x_288_; lean_object* v___x_289_; uint8_t v___x_290_; 
lean_dec(v_val_286_);
v___x_288_ = lean_array_get_size(v_keyArray_260_);
v___x_289_ = lean_nat_add(v_x_248_, v_one_273_);
lean_dec(v_x_248_);
v___x_290_ = lean_nat_dec_lt(v___x_289_, v___x_288_);
if (v___x_290_ == 0)
{
lean_dec(v___x_289_);
v_x_247_ = v_n_274_;
v_x_248_ = v_zero_249_;
goto _start;
}
else
{
v_x_247_ = v_n_274_;
v_x_248_ = v___x_289_;
goto _start;
}
}
else
{
lean_object* v_val_293_; lean_object* v___x_294_; 
lean_dec(v_n_274_);
lean_dec(v_x_246_);
lean_inc(v___x_284_);
v_val_293_ = lean_noption_get(v___x_284_);
v___x_294_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_294_, 0, v_x_248_);
lean_ctor_set(v___x_294_, 1, v_val_286_);
lean_ctor_set(v___x_294_, 2, v_val_293_);
return v___x_294_;
}
}
}
v___jp_275_:
{
lean_object* v___x_277_; lean_object* v___x_278_; uint8_t v___x_279_; 
v___x_277_ = lean_array_get_size(v_keyArray_260_);
v___x_278_ = lean_nat_add(v_x_248_, v_one_273_);
lean_dec(v_x_248_);
v___x_279_ = lean_nat_dec_lt(v___x_278_, v___x_277_);
if (v___x_279_ == 0)
{
lean_dec(v___x_278_);
v_x_246_ = v___y_276_;
v_x_247_ = v_n_274_;
v_x_248_ = v_zero_249_;
goto _start;
}
else
{
v_x_246_ = v___y_276_;
v_x_247_ = v_n_274_;
v_x_248_ = v___x_278_;
goto _start;
}
}
v___jp_282_:
{
if (lean_obj_tag(v_x_246_) == 0)
{
lean_object* v___x_283_; 
lean_inc(v_x_248_);
v___x_283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_283_, 0, v_x_248_);
v___y_276_ = v___x_283_;
goto v___jp_275_;
}
else
{
v___y_276_ = v_x_246_;
goto v___jp_275_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__0___redArg___boxed(lean_object* v_m_295_, lean_object* v_query_296_, lean_object* v_x_297_, lean_object* v_x_298_, lean_object* v_x_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__0___redArg(v_m_295_, v_query_296_, v_x_297_, v_x_298_, v_x_299_);
lean_dec_ref(v_query_296_);
lean_dec_ref(v_m_295_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0___redArg(lean_object* v_m_301_, lean_object* v_query_302_){
_start:
{
lean_object* v_keyArray_303_; lean_object* v___x_304_; uint64_t v___x_305_; uint64_t v___x_306_; uint64_t v___x_307_; uint64_t v_fold_308_; uint64_t v___x_309_; uint64_t v___x_310_; uint64_t v___x_311_; size_t v___x_312_; size_t v___x_313_; size_t v___x_314_; size_t v___x_315_; size_t v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v_keyArray_303_ = lean_ctor_get(v_m_301_, 1);
v___x_304_ = lean_array_get_size(v_keyArray_303_);
v___x_305_ = l_Lean_ExprStructEq_hash(v_query_302_);
v___x_306_ = 32ULL;
v___x_307_ = lean_uint64_shift_right(v___x_305_, v___x_306_);
v_fold_308_ = lean_uint64_xor(v___x_305_, v___x_307_);
v___x_309_ = 16ULL;
v___x_310_ = lean_uint64_shift_right(v_fold_308_, v___x_309_);
v___x_311_ = lean_uint64_xor(v_fold_308_, v___x_310_);
v___x_312_ = lean_uint64_to_usize(v___x_311_);
v___x_313_ = lean_usize_of_nat(v___x_304_);
v___x_314_ = ((size_t)1ULL);
v___x_315_ = lean_usize_sub(v___x_313_, v___x_314_);
v___x_316_ = lean_usize_land(v___x_312_, v___x_315_);
v___x_317_ = lean_usize_to_nat(v___x_316_);
v___x_318_ = lean_box(0);
v___x_319_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__0___redArg(v_m_301_, v_query_302_, v___x_318_, v___x_304_, v___x_317_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0___redArg___boxed(lean_object* v_m_320_, lean_object* v_query_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0___redArg(v_m_320_, v_query_321_);
lean_dec_ref(v_query_321_);
lean_dec_ref(v_m_320_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2_spec__4___redArg(lean_object* v_m_323_, lean_object* v_query_324_){
_start:
{
lean_object* v___x_325_; 
v___x_325_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0___redArg(v_m_323_, v_query_324_);
if (lean_obj_tag(v___x_325_) == 0)
{
lean_object* v_index_326_; lean_object* v_key_327_; lean_object* v_value_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_335_; 
v_index_326_ = lean_ctor_get(v___x_325_, 0);
v_key_327_ = lean_ctor_get(v___x_325_, 1);
v_value_328_ = lean_ctor_get(v___x_325_, 2);
v_isSharedCheck_335_ = !lean_is_exclusive(v___x_325_);
if (v_isSharedCheck_335_ == 0)
{
v___x_330_ = v___x_325_;
v_isShared_331_ = v_isSharedCheck_335_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_value_328_);
lean_inc(v_key_327_);
lean_inc(v_index_326_);
lean_dec(v___x_325_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_335_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v___x_333_; 
if (v_isShared_331_ == 0)
{
v___x_333_ = v___x_330_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v_index_326_);
lean_ctor_set(v_reuseFailAlloc_334_, 1, v_key_327_);
lean_ctor_set(v_reuseFailAlloc_334_, 2, v_value_328_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
}
else
{
lean_object* v___x_336_; 
lean_dec(v___x_325_);
v___x_336_ = lean_box(1);
return v___x_336_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2_spec__4___redArg___boxed(lean_object* v_m_337_, lean_object* v_query_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2_spec__4___redArg(v_m_337_, v_query_338_);
lean_dec_ref(v_query_338_);
lean_dec_ref(v_m_337_);
return v_res_339_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2___redArg(lean_object* v_m_340_, lean_object* v_a_341_){
_start:
{
lean_object* v___x_342_; 
v___x_342_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2_spec__4___redArg(v_m_340_, v_a_341_);
if (lean_obj_tag(v___x_342_) == 0)
{
lean_object* v_value_343_; lean_object* v___x_344_; 
v_value_343_ = lean_ctor_get(v___x_342_, 2);
lean_inc(v_value_343_);
lean_dec_ref_known(v___x_342_, 3);
v___x_344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_344_, 0, v_value_343_);
return v___x_344_;
}
else
{
lean_object* v___x_345_; 
v___x_345_ = lean_box(0);
return v___x_345_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2___redArg___boxed(lean_object* v_m_346_, lean_object* v_a_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2___redArg(v_m_346_, v_a_347_);
lean_dec_ref(v_a_347_);
lean_dec_ref(v_m_346_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1_spec__2_spec__4___redArg(lean_object* v_b_349_, lean_object* v_acc_350_, lean_object* v_i_351_){
_start:
{
lean_object* v___y_353_; lean_object* v_keyArray_361_; lean_object* v_valueArray_362_; lean_object* v___x_363_; uint8_t v___x_364_; 
v_keyArray_361_ = lean_ctor_get(v_b_349_, 1);
v_valueArray_362_ = lean_ctor_get(v_b_349_, 2);
v___x_363_ = lean_array_get_size(v_keyArray_361_);
v___x_364_ = lean_nat_dec_lt(v_i_351_, v___x_363_);
if (v___x_364_ == 0)
{
lean_dec(v_i_351_);
return v_acc_350_;
}
else
{
lean_object* v___x_365_; uint8_t v_isSome_366_; 
v___x_365_ = lean_array_fget_borrowed(v_keyArray_361_, v_i_351_);
v_isSome_366_ = lean_noption_is_some(v___x_365_);
if (v_isSome_366_ == 0)
{
goto v___jp_357_;
}
else
{
lean_object* v___x_367_; uint8_t v_isSome_368_; 
v___x_367_ = lean_array_fget_borrowed(v_valueArray_362_, v_i_351_);
v_isSome_368_ = lean_noption_is_some(v___x_367_);
if (v_isSome_368_ == 0)
{
goto v___jp_357_;
}
else
{
lean_object* v_val_369_; lean_object* v_val_370_; lean_object* v_i_372_; lean_object* v___x_377_; 
lean_inc(v___x_365_);
v_val_369_ = lean_noption_get(v___x_365_);
lean_inc(v___x_367_);
v_val_370_ = lean_noption_get(v___x_367_);
v___x_377_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0___redArg(v_acc_350_, v_val_369_);
switch(lean_obj_tag(v___x_377_))
{
case 0:
{
lean_object* v_index_378_; lean_object* v_size_379_; lean_object* v___x_380_; 
v_index_378_ = lean_ctor_get(v___x_377_, 0);
lean_inc(v_index_378_);
lean_dec_ref_known(v___x_377_, 3);
v_size_379_ = lean_ctor_get(v_acc_350_, 0);
lean_inc(v_size_379_);
v___x_380_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_350_, v_size_379_, v_index_378_, v_val_369_, v_val_370_);
lean_dec(v_index_378_);
v___y_353_ = v___x_380_;
goto v___jp_352_;
}
case 1:
{
lean_object* v_index_381_; 
v_index_381_ = lean_ctor_get(v___x_377_, 0);
lean_inc(v_index_381_);
lean_dec_ref_known(v___x_377_, 1);
v_i_372_ = v_index_381_;
goto v___jp_371_;
}
default: 
{
lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_382_ = lean_unsigned_to_nat(0u);
v___x_383_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_350_, v___x_382_);
if (lean_obj_tag(v___x_383_) == 0)
{
lean_object* v_index_384_; 
v_index_384_ = lean_ctor_get(v___x_383_, 0);
lean_inc(v_index_384_);
lean_dec_ref_known(v___x_383_, 1);
v_i_372_ = v_index_384_;
goto v___jp_371_;
}
else
{
lean_dec(v_val_370_);
lean_dec(v_val_369_);
v___y_353_ = v_acc_350_;
goto v___jp_352_;
}
}
}
v___jp_371_:
{
lean_object* v_size_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v_size_373_ = lean_ctor_get(v_acc_350_, 0);
v___x_374_ = lean_unsigned_to_nat(1u);
v___x_375_ = lean_nat_add(v_size_373_, v___x_374_);
v___x_376_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_350_, v___x_375_, v_i_372_, v_val_369_, v_val_370_);
lean_dec(v_i_372_);
v___y_353_ = v___x_376_;
goto v___jp_352_;
}
}
}
}
v___jp_352_:
{
lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_354_ = lean_unsigned_to_nat(1u);
v___x_355_ = lean_nat_add(v_i_351_, v___x_354_);
lean_dec(v_i_351_);
v_acc_350_ = v___y_353_;
v_i_351_ = v___x_355_;
goto _start;
}
v___jp_357_:
{
lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_358_ = lean_unsigned_to_nat(1u);
v___x_359_ = lean_nat_add(v_i_351_, v___x_358_);
lean_dec(v_i_351_);
v_i_351_ = v___x_359_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_b_385_, lean_object* v_acc_386_, lean_object* v_i_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1_spec__2_spec__4___redArg(v_b_385_, v_acc_386_, v_i_387_);
lean_dec_ref(v_b_385_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1_spec__2___redArg(lean_object* v_init_389_, lean_object* v_b_390_){
_start:
{
lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_391_ = lean_unsigned_to_nat(0u);
v___x_392_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1_spec__2_spec__4___redArg(v_b_390_, v_init_389_, v___x_391_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1_spec__2___redArg___boxed(lean_object* v_init_393_, lean_object* v_b_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1_spec__2___redArg(v_init_393_, v_b_394_);
lean_dec_ref(v_b_394_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1___redArg(lean_object* v_m_396_){
_start:
{
lean_object* v_keyArray_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v_cellCount_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v_target_404_; lean_object* v___x_405_; 
v_keyArray_397_ = lean_ctor_get(v_m_396_, 1);
v___x_398_ = lean_array_get_size(v_keyArray_397_);
v___x_399_ = lean_unsigned_to_nat(2u);
v_cellCount_400_ = lean_nat_mul(v___x_398_, v___x_399_);
v___x_401_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_400_);
v___x_402_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_400_);
v___x_403_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_400_);
v_target_404_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_404_, 0, v___x_401_);
lean_ctor_set(v_target_404_, 1, v___x_402_);
lean_ctor_set(v_target_404_, 2, v___x_403_);
v___x_405_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1_spec__2___redArg(v_target_404_, v_m_396_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1___redArg___boxed(lean_object* v_m_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1___redArg(v_m_406_);
lean_dec_ref(v_m_406_);
return v_res_407_;
}
}
static lean_object* _init_l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___closed__2(void){
_start:
{
lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_410_ = ((lean_object*)(l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___closed__1));
v___x_411_ = lean_unsigned_to_nat(10u);
v___x_412_ = lean_unsigned_to_nat(72u);
v___x_413_ = ((lean_object*)(l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___closed__0));
v___x_414_ = ((lean_object*)(l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope___closed__0));
v___x_415_ = l_mkPanicMessageWithDecl(v___x_414_, v___x_413_, v___x_412_, v___x_411_, v___x_410_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go(lean_object* v_e_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_){
_start:
{
lean_object* v___y_423_; lean_object* v___y_424_; lean_object* v___y_428_; lean_object* v___y_429_; lean_object* v___y_430_; lean_object* v_i_431_; lean_object* v___y_437_; lean_object* v___y_438_; lean_object* v___y_439_; lean_object* v___y_449_; lean_object* v___y_450_; lean_object* v___y_451_; lean_object* v_i_452_; lean_object* v___y_458_; lean_object* v___y_459_; lean_object* v___y_460_; lean_object* v_a_471_; lean_object* v_fst_472_; lean_object* v___y_505_; lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_508_ = lean_st_ref_get(v_a_417_);
v___x_509_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2___redArg(v___x_508_, v_e_416_);
lean_dec(v___x_508_);
if (lean_obj_tag(v___x_509_) == 0)
{
lean_object* v___x_510_; lean_object* v___x_511_; uint8_t v___x_512_; 
v___x_510_ = ((lean_object*)(l_Lean_Expr_hasBinderNameHint___lam__0___closed__1));
v___x_511_ = lean_unsigned_to_nat(6u);
v___x_512_ = l_Lean_Expr_isAppOfArity(v_e_416_, v___x_510_, v___x_511_);
if (v___x_512_ == 0)
{
switch(lean_obj_tag(v_e_416_))
{
case 7:
{
lean_object* v_binderName_513_; lean_object* v_binderType_514_; lean_object* v_body_515_; uint8_t v_binderInfo_516_; lean_object* v___x_517_; 
v_binderName_513_ = lean_ctor_get(v_e_416_, 0);
v_binderType_514_ = lean_ctor_get(v_e_416_, 1);
v_body_515_ = lean_ctor_get(v_e_416_, 2);
v_binderInfo_516_ = lean_ctor_get_uint8(v_e_416_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_514_);
v___x_517_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go(v_binderType_514_, v_a_417_, v_a_418_, v_a_419_, v_a_420_);
if (lean_obj_tag(v___x_517_) == 0)
{
lean_object* v_a_518_; lean_object* v_fst_519_; lean_object* v_snd_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v_a_518_ = lean_ctor_get(v___x_517_, 0);
lean_inc(v_a_518_);
lean_dec_ref_known(v___x_517_, 1);
v_fst_519_ = lean_ctor_get(v_a_518_, 0);
lean_inc(v_fst_519_);
v_snd_520_ = lean_ctor_get(v_a_518_, 1);
lean_inc(v_snd_520_);
lean_dec(v_a_518_);
lean_inc(v_binderName_513_);
v___x_521_ = lean_array_push(v_snd_520_, v_binderName_513_);
lean_inc_ref(v_body_515_);
v___x_522_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go(v_body_515_, v_a_417_, v___x_521_, v_a_419_, v_a_420_);
if (lean_obj_tag(v___x_522_) == 0)
{
lean_object* v_a_523_; lean_object* v_fst_524_; lean_object* v_snd_525_; lean_object* v___x_526_; lean_object* v_fst_527_; lean_object* v_snd_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_536_; 
v_a_523_ = lean_ctor_get(v___x_522_, 0);
lean_inc(v_a_523_);
lean_dec_ref_known(v___x_522_, 1);
v_fst_524_ = lean_ctor_get(v_a_523_, 0);
lean_inc(v_fst_524_);
v_snd_525_ = lean_ctor_get(v_a_523_, 1);
lean_inc(v_snd_525_);
lean_dec(v_a_523_);
v___x_526_ = l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope(v_snd_525_);
v_fst_527_ = lean_ctor_get(v___x_526_, 0);
v_snd_528_ = lean_ctor_get(v___x_526_, 1);
v_isSharedCheck_536_ = !lean_is_exclusive(v___x_526_);
if (v_isSharedCheck_536_ == 0)
{
v___x_530_ = v___x_526_;
v_isShared_531_ = v_isSharedCheck_536_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_snd_528_);
lean_inc(v_fst_527_);
lean_dec(v___x_526_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_536_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_532_; lean_object* v___x_534_; 
v___x_532_ = l_Lean_Expr_forallE___override(v_fst_527_, v_fst_519_, v_fst_524_, v_binderInfo_516_);
lean_inc_ref(v___x_532_);
if (v_isShared_531_ == 0)
{
lean_ctor_set(v___x_530_, 0, v___x_532_);
v___x_534_ = v___x_530_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v___x_532_);
lean_ctor_set(v_reuseFailAlloc_535_, 1, v_snd_528_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
v_a_471_ = v___x_534_;
v_fst_472_ = v___x_532_;
goto v___jp_470_;
}
}
}
else
{
lean_dec(v_fst_519_);
v___y_505_ = v___x_522_;
goto v___jp_504_;
}
}
else
{
v___y_505_ = v___x_517_;
goto v___jp_504_;
}
}
case 6:
{
lean_object* v_binderName_537_; lean_object* v_binderType_538_; lean_object* v_body_539_; uint8_t v_binderInfo_540_; lean_object* v___x_541_; 
v_binderName_537_ = lean_ctor_get(v_e_416_, 0);
v_binderType_538_ = lean_ctor_get(v_e_416_, 1);
v_body_539_ = lean_ctor_get(v_e_416_, 2);
v_binderInfo_540_ = lean_ctor_get_uint8(v_e_416_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_538_);
v___x_541_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go(v_binderType_538_, v_a_417_, v_a_418_, v_a_419_, v_a_420_);
if (lean_obj_tag(v___x_541_) == 0)
{
lean_object* v_a_542_; lean_object* v_fst_543_; lean_object* v_snd_544_; lean_object* v___x_545_; lean_object* v___x_546_; 
v_a_542_ = lean_ctor_get(v___x_541_, 0);
lean_inc(v_a_542_);
lean_dec_ref_known(v___x_541_, 1);
v_fst_543_ = lean_ctor_get(v_a_542_, 0);
lean_inc(v_fst_543_);
v_snd_544_ = lean_ctor_get(v_a_542_, 1);
lean_inc(v_snd_544_);
lean_dec(v_a_542_);
lean_inc(v_binderName_537_);
v___x_545_ = lean_array_push(v_snd_544_, v_binderName_537_);
lean_inc_ref(v_body_539_);
v___x_546_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go(v_body_539_, v_a_417_, v___x_545_, v_a_419_, v_a_420_);
if (lean_obj_tag(v___x_546_) == 0)
{
lean_object* v_a_547_; lean_object* v_fst_548_; lean_object* v_snd_549_; lean_object* v___x_550_; lean_object* v_fst_551_; lean_object* v_snd_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_560_; 
v_a_547_ = lean_ctor_get(v___x_546_, 0);
lean_inc(v_a_547_);
lean_dec_ref_known(v___x_546_, 1);
v_fst_548_ = lean_ctor_get(v_a_547_, 0);
lean_inc(v_fst_548_);
v_snd_549_ = lean_ctor_get(v_a_547_, 1);
lean_inc(v_snd_549_);
lean_dec(v_a_547_);
v___x_550_ = l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope(v_snd_549_);
v_fst_551_ = lean_ctor_get(v___x_550_, 0);
v_snd_552_ = lean_ctor_get(v___x_550_, 1);
v_isSharedCheck_560_ = !lean_is_exclusive(v___x_550_);
if (v_isSharedCheck_560_ == 0)
{
v___x_554_ = v___x_550_;
v_isShared_555_ = v_isSharedCheck_560_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_snd_552_);
lean_inc(v_fst_551_);
lean_dec(v___x_550_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_560_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v___x_556_; lean_object* v___x_558_; 
v___x_556_ = l_Lean_Expr_lam___override(v_fst_551_, v_fst_543_, v_fst_548_, v_binderInfo_540_);
lean_inc_ref(v___x_556_);
if (v_isShared_555_ == 0)
{
lean_ctor_set(v___x_554_, 0, v___x_556_);
v___x_558_ = v___x_554_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v___x_556_);
lean_ctor_set(v_reuseFailAlloc_559_, 1, v_snd_552_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
v_a_471_ = v___x_558_;
v_fst_472_ = v___x_556_;
goto v___jp_470_;
}
}
}
else
{
lean_dec(v_fst_543_);
v___y_505_ = v___x_546_;
goto v___jp_504_;
}
}
else
{
v___y_505_ = v___x_541_;
goto v___jp_504_;
}
}
case 8:
{
lean_object* v_declName_561_; lean_object* v_type_562_; lean_object* v_value_563_; lean_object* v_body_564_; uint8_t v_nondep_565_; lean_object* v___x_566_; 
v_declName_561_ = lean_ctor_get(v_e_416_, 0);
v_type_562_ = lean_ctor_get(v_e_416_, 1);
v_value_563_ = lean_ctor_get(v_e_416_, 2);
v_body_564_ = lean_ctor_get(v_e_416_, 3);
v_nondep_565_ = lean_ctor_get_uint8(v_e_416_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_562_);
v___x_566_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go(v_type_562_, v_a_417_, v_a_418_, v_a_419_, v_a_420_);
if (lean_obj_tag(v___x_566_) == 0)
{
lean_object* v_a_567_; lean_object* v_fst_568_; lean_object* v_snd_569_; lean_object* v___x_570_; 
v_a_567_ = lean_ctor_get(v___x_566_, 0);
lean_inc(v_a_567_);
lean_dec_ref_known(v___x_566_, 1);
v_fst_568_ = lean_ctor_get(v_a_567_, 0);
lean_inc(v_fst_568_);
v_snd_569_ = lean_ctor_get(v_a_567_, 1);
lean_inc(v_snd_569_);
lean_dec(v_a_567_);
lean_inc_ref(v_value_563_);
v___x_570_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go(v_value_563_, v_a_417_, v_snd_569_, v_a_419_, v_a_420_);
if (lean_obj_tag(v___x_570_) == 0)
{
lean_object* v_a_571_; lean_object* v_fst_572_; lean_object* v_snd_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v_a_571_ = lean_ctor_get(v___x_570_, 0);
lean_inc(v_a_571_);
lean_dec_ref_known(v___x_570_, 1);
v_fst_572_ = lean_ctor_get(v_a_571_, 0);
lean_inc(v_fst_572_);
v_snd_573_ = lean_ctor_get(v_a_571_, 1);
lean_inc(v_snd_573_);
lean_dec(v_a_571_);
lean_inc(v_declName_561_);
v___x_574_ = lean_array_push(v_snd_573_, v_declName_561_);
lean_inc_ref(v_body_564_);
v___x_575_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go(v_body_564_, v_a_417_, v___x_574_, v_a_419_, v_a_420_);
if (lean_obj_tag(v___x_575_) == 0)
{
lean_object* v_a_576_; lean_object* v_fst_577_; lean_object* v_snd_578_; lean_object* v___x_579_; lean_object* v_fst_580_; lean_object* v_snd_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_589_; 
v_a_576_ = lean_ctor_get(v___x_575_, 0);
lean_inc(v_a_576_);
lean_dec_ref_known(v___x_575_, 1);
v_fst_577_ = lean_ctor_get(v_a_576_, 0);
lean_inc(v_fst_577_);
v_snd_578_ = lean_ctor_get(v_a_576_, 1);
lean_inc(v_snd_578_);
lean_dec(v_a_576_);
v___x_579_ = l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope(v_snd_578_);
v_fst_580_ = lean_ctor_get(v___x_579_, 0);
v_snd_581_ = lean_ctor_get(v___x_579_, 1);
v_isSharedCheck_589_ = !lean_is_exclusive(v___x_579_);
if (v_isSharedCheck_589_ == 0)
{
v___x_583_ = v___x_579_;
v_isShared_584_ = v_isSharedCheck_589_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_snd_581_);
lean_inc(v_fst_580_);
lean_dec(v___x_579_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_589_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_585_; lean_object* v___x_587_; 
v___x_585_ = l_Lean_Expr_letE___override(v_fst_580_, v_fst_568_, v_fst_572_, v_fst_577_, v_nondep_565_);
lean_inc_ref(v___x_585_);
if (v_isShared_584_ == 0)
{
lean_ctor_set(v___x_583_, 0, v___x_585_);
v___x_587_ = v___x_583_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v___x_585_);
lean_ctor_set(v_reuseFailAlloc_588_, 1, v_snd_581_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
v_a_471_ = v___x_587_;
v_fst_472_ = v___x_585_;
goto v___jp_470_;
}
}
}
else
{
lean_dec(v_fst_572_);
lean_dec(v_fst_568_);
v___y_505_ = v___x_575_;
goto v___jp_504_;
}
}
else
{
lean_dec(v_fst_568_);
v___y_505_ = v___x_570_;
goto v___jp_504_;
}
}
else
{
v___y_505_ = v___x_566_;
goto v___jp_504_;
}
}
case 5:
{
lean_object* v_fn_590_; lean_object* v_arg_591_; lean_object* v___x_592_; 
v_fn_590_ = lean_ctor_get(v_e_416_, 0);
v_arg_591_ = lean_ctor_get(v_e_416_, 1);
lean_inc_ref(v_fn_590_);
v___x_592_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go(v_fn_590_, v_a_417_, v_a_418_, v_a_419_, v_a_420_);
if (lean_obj_tag(v___x_592_) == 0)
{
lean_object* v_a_593_; lean_object* v_fst_594_; lean_object* v_snd_595_; lean_object* v___x_596_; 
v_a_593_ = lean_ctor_get(v___x_592_, 0);
lean_inc(v_a_593_);
lean_dec_ref_known(v___x_592_, 1);
v_fst_594_ = lean_ctor_get(v_a_593_, 0);
lean_inc(v_fst_594_);
v_snd_595_ = lean_ctor_get(v_a_593_, 1);
lean_inc(v_snd_595_);
lean_dec(v_a_593_);
lean_inc_ref(v_arg_591_);
v___x_596_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go(v_arg_591_, v_a_417_, v_snd_595_, v_a_419_, v_a_420_);
if (lean_obj_tag(v___x_596_) == 0)
{
lean_object* v_a_597_; lean_object* v_fst_598_; lean_object* v_snd_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_617_; 
v_a_597_ = lean_ctor_get(v___x_596_, 0);
lean_inc(v_a_597_);
lean_dec_ref_known(v___x_596_, 1);
v_fst_598_ = lean_ctor_get(v_a_597_, 0);
v_snd_599_ = lean_ctor_get(v_a_597_, 1);
v_isSharedCheck_617_ = !lean_is_exclusive(v_a_597_);
if (v_isSharedCheck_617_ == 0)
{
v___x_601_ = v_a_597_;
v_isShared_602_ = v_isSharedCheck_617_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_snd_599_);
lean_inc(v_fst_598_);
lean_dec(v_a_597_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_617_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v___y_604_; uint8_t v___y_609_; size_t v___x_611_; size_t v___x_612_; uint8_t v___x_613_; 
v___x_611_ = lean_ptr_addr(v_fn_590_);
v___x_612_ = lean_ptr_addr(v_fst_594_);
v___x_613_ = lean_usize_dec_eq(v___x_611_, v___x_612_);
if (v___x_613_ == 0)
{
v___y_609_ = v___x_613_;
goto v___jp_608_;
}
else
{
size_t v___x_614_; size_t v___x_615_; uint8_t v___x_616_; 
v___x_614_ = lean_ptr_addr(v_arg_591_);
v___x_615_ = lean_ptr_addr(v_fst_598_);
v___x_616_ = lean_usize_dec_eq(v___x_614_, v___x_615_);
v___y_609_ = v___x_616_;
goto v___jp_608_;
}
v___jp_603_:
{
lean_object* v___x_606_; 
lean_inc_ref(v___y_604_);
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 0, v___y_604_);
v___x_606_ = v___x_601_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v___y_604_);
lean_ctor_set(v_reuseFailAlloc_607_, 1, v_snd_599_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
v_a_471_ = v___x_606_;
v_fst_472_ = v___y_604_;
goto v___jp_470_;
}
}
v___jp_608_:
{
if (v___y_609_ == 0)
{
lean_object* v___x_610_; 
v___x_610_ = l_Lean_Expr_app___override(v_fst_594_, v_fst_598_);
v___y_604_ = v___x_610_;
goto v___jp_603_;
}
else
{
lean_dec(v_fst_598_);
lean_dec(v_fst_594_);
lean_inc_ref(v_e_416_);
v___y_604_ = v_e_416_;
goto v___jp_603_;
}
}
}
}
else
{
lean_dec(v_fst_594_);
v___y_505_ = v___x_596_;
goto v___jp_504_;
}
}
else
{
v___y_505_ = v___x_592_;
goto v___jp_504_;
}
}
case 10:
{
lean_object* v_data_618_; lean_object* v_expr_619_; lean_object* v___x_620_; 
v_data_618_ = lean_ctor_get(v_e_416_, 0);
v_expr_619_ = lean_ctor_get(v_e_416_, 1);
lean_inc_ref(v_expr_619_);
v___x_620_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go(v_expr_619_, v_a_417_, v_a_418_, v_a_419_, v_a_420_);
if (lean_obj_tag(v___x_620_) == 0)
{
lean_object* v_a_621_; lean_object* v_fst_622_; lean_object* v_snd_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_636_; 
v_a_621_ = lean_ctor_get(v___x_620_, 0);
lean_inc(v_a_621_);
lean_dec_ref_known(v___x_620_, 1);
v_fst_622_ = lean_ctor_get(v_a_621_, 0);
v_snd_623_ = lean_ctor_get(v_a_621_, 1);
v_isSharedCheck_636_ = !lean_is_exclusive(v_a_621_);
if (v_isSharedCheck_636_ == 0)
{
v___x_625_ = v_a_621_;
v_isShared_626_ = v_isSharedCheck_636_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_snd_623_);
lean_inc(v_fst_622_);
lean_dec(v_a_621_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_636_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___y_628_; size_t v___x_632_; size_t v___x_633_; uint8_t v___x_634_; 
v___x_632_ = lean_ptr_addr(v_expr_619_);
v___x_633_ = lean_ptr_addr(v_fst_622_);
v___x_634_ = lean_usize_dec_eq(v___x_632_, v___x_633_);
if (v___x_634_ == 0)
{
lean_object* v___x_635_; 
lean_inc(v_data_618_);
v___x_635_ = l_Lean_Expr_mdata___override(v_data_618_, v_fst_622_);
v___y_628_ = v___x_635_;
goto v___jp_627_;
}
else
{
lean_dec(v_fst_622_);
lean_inc_ref(v_e_416_);
v___y_628_ = v_e_416_;
goto v___jp_627_;
}
v___jp_627_:
{
lean_object* v___x_630_; 
lean_inc_ref(v___y_628_);
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 0, v___y_628_);
v___x_630_ = v___x_625_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v___y_628_);
lean_ctor_set(v_reuseFailAlloc_631_, 1, v_snd_623_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
v_a_471_ = v___x_630_;
v_fst_472_ = v___y_628_;
goto v___jp_470_;
}
}
}
}
else
{
v___y_505_ = v___x_620_;
goto v___jp_504_;
}
}
case 11:
{
lean_object* v_typeName_637_; lean_object* v_idx_638_; lean_object* v_struct_639_; lean_object* v___x_640_; 
v_typeName_637_ = lean_ctor_get(v_e_416_, 0);
v_idx_638_ = lean_ctor_get(v_e_416_, 1);
v_struct_639_ = lean_ctor_get(v_e_416_, 2);
lean_inc_ref(v_struct_639_);
v___x_640_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go(v_struct_639_, v_a_417_, v_a_418_, v_a_419_, v_a_420_);
if (lean_obj_tag(v___x_640_) == 0)
{
lean_object* v_a_641_; lean_object* v_fst_642_; lean_object* v_snd_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_656_; 
v_a_641_ = lean_ctor_get(v___x_640_, 0);
lean_inc(v_a_641_);
lean_dec_ref_known(v___x_640_, 1);
v_fst_642_ = lean_ctor_get(v_a_641_, 0);
v_snd_643_ = lean_ctor_get(v_a_641_, 1);
v_isSharedCheck_656_ = !lean_is_exclusive(v_a_641_);
if (v_isSharedCheck_656_ == 0)
{
v___x_645_ = v_a_641_;
v_isShared_646_ = v_isSharedCheck_656_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_snd_643_);
lean_inc(v_fst_642_);
lean_dec(v_a_641_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_656_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___y_648_; size_t v___x_652_; size_t v___x_653_; uint8_t v___x_654_; 
v___x_652_ = lean_ptr_addr(v_struct_639_);
v___x_653_ = lean_ptr_addr(v_fst_642_);
v___x_654_ = lean_usize_dec_eq(v___x_652_, v___x_653_);
if (v___x_654_ == 0)
{
lean_object* v___x_655_; 
lean_inc(v_idx_638_);
lean_inc(v_typeName_637_);
v___x_655_ = l_Lean_Expr_proj___override(v_typeName_637_, v_idx_638_, v_fst_642_);
v___y_648_ = v___x_655_;
goto v___jp_647_;
}
else
{
lean_dec(v_fst_642_);
lean_inc_ref(v_e_416_);
v___y_648_ = v_e_416_;
goto v___jp_647_;
}
v___jp_647_:
{
lean_object* v___x_650_; 
lean_inc_ref(v___y_648_);
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 0, v___y_648_);
v___x_650_ = v___x_645_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v___y_648_);
lean_ctor_set(v_reuseFailAlloc_651_, 1, v_snd_643_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
v_a_471_ = v___x_650_;
v_fst_472_ = v___y_648_;
goto v___jp_470_;
}
}
}
}
else
{
v___y_505_ = v___x_640_;
goto v___jp_504_;
}
}
default: 
{
lean_object* v___x_657_; 
lean_inc_ref_n(v_e_416_, 2);
v___x_657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_657_, 0, v_e_416_);
lean_ctor_set(v___x_657_, 1, v_a_418_);
v_a_471_ = v___x_657_;
v_fst_472_ = v_e_416_;
goto v___jp_470_;
}
}
}
else
{
lean_object* v_e_658_; lean_object* v___x_659_; 
v_e_658_ = l_Lean_Expr_appArg_x21(v_e_416_);
v___x_659_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go(v_e_658_, v_a_417_, v_a_418_, v_a_419_, v_a_420_);
if (lean_obj_tag(v___x_659_) == 0)
{
lean_object* v_a_660_; lean_object* v_fst_661_; lean_object* v_snd_662_; lean_object* v___f_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v_v_666_; 
v_a_660_ = lean_ctor_get(v___x_659_, 0);
lean_inc(v_a_660_);
lean_dec_ref_known(v___x_659_, 1);
v_fst_661_ = lean_ctor_get(v_a_660_, 0);
lean_inc_n(v_fst_661_, 2);
v_snd_662_ = lean_ctor_get(v_a_660_, 1);
lean_inc(v_snd_662_);
lean_dec(v_a_660_);
v___f_663_ = lean_alloc_closure((void*)(l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___lam__0___boxed), 7, 1);
lean_closure_set(v___f_663_, 0, v_fst_661_);
v___x_664_ = l_Lean_Expr_appFn_x21(v_e_416_);
v___x_665_ = l_Lean_Expr_appFn_x21(v___x_664_);
v_v_666_ = l_Lean_Expr_appArg_x21(v___x_665_);
lean_dec_ref(v___x_665_);
if (lean_obj_tag(v_v_666_) == 0)
{
lean_object* v_deBruijnIndex_667_; lean_object* v_b_668_; lean_object* v___x_669_; 
v_deBruijnIndex_667_ = lean_ctor_get(v_v_666_, 0);
lean_inc(v_deBruijnIndex_667_);
lean_dec_ref_known(v_v_666_, 1);
v_b_668_ = l_Lean_Expr_appArg_x21(v___x_664_);
lean_dec_ref(v___x_664_);
v___x_669_ = l_Lean_Expr_headBeta(v_b_668_);
switch(lean_obj_tag(v___x_669_))
{
case 6:
{
lean_object* v_binderName_670_; lean_object* v_binderType_671_; lean_object* v_body_672_; uint8_t v_binderInfo_673_; lean_object* v___x_674_; 
lean_dec(v_fst_661_);
v_binderName_670_ = lean_ctor_get(v___x_669_, 0);
lean_inc(v_binderName_670_);
v_binderType_671_ = lean_ctor_get(v___x_669_, 1);
lean_inc_ref(v_binderType_671_);
v_body_672_ = lean_ctor_get(v___x_669_, 2);
lean_inc_ref(v_body_672_);
v_binderInfo_673_ = lean_ctor_get_uint8(v___x_669_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v___x_669_, 3);
v___x_674_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___lam__1(v___f_663_, v_deBruijnIndex_667_, v_binderName_670_, v_binderType_671_, v_body_672_, v_binderInfo_673_, v_a_417_, v_snd_662_, v_a_419_, v_a_420_);
lean_dec_ref(v_body_672_);
lean_dec_ref(v_binderType_671_);
lean_dec(v_deBruijnIndex_667_);
v___y_505_ = v___x_674_;
goto v___jp_504_;
}
case 7:
{
lean_object* v_binderName_675_; lean_object* v_binderType_676_; lean_object* v_body_677_; uint8_t v_binderInfo_678_; lean_object* v___x_679_; 
lean_dec(v_fst_661_);
v_binderName_675_ = lean_ctor_get(v___x_669_, 0);
lean_inc(v_binderName_675_);
v_binderType_676_ = lean_ctor_get(v___x_669_, 1);
lean_inc_ref(v_binderType_676_);
v_body_677_ = lean_ctor_get(v___x_669_, 2);
lean_inc_ref(v_body_677_);
v_binderInfo_678_ = lean_ctor_get_uint8(v___x_669_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v___x_669_, 3);
v___x_679_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___lam__1(v___f_663_, v_deBruijnIndex_667_, v_binderName_675_, v_binderType_676_, v_body_677_, v_binderInfo_678_, v_a_417_, v_snd_662_, v_a_419_, v_a_420_);
lean_dec_ref(v_body_677_);
lean_dec_ref(v_binderType_676_);
lean_dec(v_deBruijnIndex_667_);
v___y_505_ = v___x_679_;
goto v___jp_504_;
}
default: 
{
lean_object* v___x_680_; uint8_t v___x_681_; 
lean_dec_ref(v___x_669_);
lean_dec_ref(v___f_663_);
v___x_680_ = lean_array_get_size(v_snd_662_);
v___x_681_ = lean_nat_dec_lt(v_deBruijnIndex_667_, v___x_680_);
if (v___x_681_ == 0)
{
lean_object* v___x_682_; lean_object* v___x_683_; 
lean_dec(v_deBruijnIndex_667_);
lean_dec(v_fst_661_);
v___x_682_ = lean_obj_once(&l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___closed__2, &l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___closed__2_once, _init_l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___closed__2);
v___x_683_ = l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__3(v___x_682_, v_a_417_, v_snd_662_, v_a_419_, v_a_420_);
v___y_505_ = v___x_683_;
goto v___jp_504_;
}
else
{
lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_684_ = lean_box(0);
v___x_685_ = lean_nat_sub(v___x_680_, v_deBruijnIndex_667_);
v___x_686_ = lean_unsigned_to_nat(1u);
v___x_687_ = lean_nat_sub(v___x_685_, v___x_686_);
lean_dec(v___x_685_);
v___x_688_ = lean_array_get_borrowed(v___x_684_, v_snd_662_, v___x_687_);
lean_dec(v___x_687_);
lean_inc(v___x_688_);
v___x_689_ = l_Lean_Core_mkFreshUserName(v___x_688_, v_a_419_, v_a_420_);
if (lean_obj_tag(v___x_689_) == 0)
{
lean_object* v_a_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v_a_690_ = lean_ctor_get(v___x_689_, 0);
lean_inc(v_a_690_);
lean_dec_ref_known(v___x_689_, 1);
v___x_691_ = lean_box(0);
v___x_692_ = l___private_Lean_Meta_BinderNameHint_0__Lean_rememberName(v_deBruijnIndex_667_, v_a_690_, v_snd_662_);
lean_dec(v_deBruijnIndex_667_);
v___x_693_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___lam__0(v_fst_661_, v___x_691_, v_a_417_, v___x_692_, v_a_419_, v_a_420_);
v___y_505_ = v___x_693_;
goto v___jp_504_;
}
else
{
lean_object* v_a_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_701_; 
lean_dec(v_deBruijnIndex_667_);
lean_dec(v_snd_662_);
lean_dec(v_fst_661_);
lean_dec_ref(v_e_416_);
v_a_694_ = lean_ctor_get(v___x_689_, 0);
v_isSharedCheck_701_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_701_ == 0)
{
v___x_696_ = v___x_689_;
v_isShared_697_ = v_isSharedCheck_701_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_a_694_);
lean_dec(v___x_689_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_701_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_699_; 
if (v_isShared_697_ == 0)
{
v___x_699_ = v___x_696_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_a_694_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_702_; lean_object* v___x_703_; 
lean_dec_ref(v_v_666_);
lean_dec_ref(v___x_664_);
lean_dec_ref(v___f_663_);
v___x_702_ = lean_box(0);
v___x_703_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___lam__0(v_fst_661_, v___x_702_, v_a_417_, v_snd_662_, v_a_419_, v_a_420_);
v___y_505_ = v___x_703_;
goto v___jp_504_;
}
}
else
{
v___y_505_ = v___x_659_;
goto v___jp_504_;
}
}
}
else
{
lean_object* v_val_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_712_; 
lean_dec_ref(v_e_416_);
v_val_704_ = lean_ctor_get(v___x_509_, 0);
v_isSharedCheck_712_ = !lean_is_exclusive(v___x_509_);
if (v_isSharedCheck_712_ == 0)
{
v___x_706_ = v___x_509_;
v_isShared_707_ = v_isSharedCheck_712_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_val_704_);
lean_dec(v___x_509_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_712_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v___x_708_; lean_object* v___x_710_; 
v___x_708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_708_, 0, v_val_704_);
lean_ctor_set(v___x_708_, 1, v_a_418_);
if (v_isShared_707_ == 0)
{
lean_ctor_set_tag(v___x_706_, 0);
lean_ctor_set(v___x_706_, 0, v___x_708_);
v___x_710_ = v___x_706_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v___x_708_);
v___x_710_ = v_reuseFailAlloc_711_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
return v___x_710_;
}
}
}
v___jp_422_:
{
lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_425_ = lean_st_ref_put(v_a_417_, v___y_424_);
v___x_426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_426_, 0, v___y_423_);
return v___x_426_;
}
v___jp_427_:
{
lean_object* v_size_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
v_size_432_ = lean_ctor_get(v___y_428_, 0);
v___x_433_ = lean_unsigned_to_nat(1u);
v___x_434_ = lean_nat_add(v_size_432_, v___x_433_);
v___x_435_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_428_, v___x_434_, v_i_431_, v_e_416_, v___y_430_);
lean_dec(v_i_431_);
v___y_423_ = v___y_429_;
v___y_424_ = v___x_435_;
goto v___jp_422_;
}
v___jp_436_:
{
lean_object* v___x_440_; 
v___x_440_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0___redArg(v___y_439_, v_e_416_);
switch(lean_obj_tag(v___x_440_))
{
case 0:
{
lean_object* v_index_441_; lean_object* v_size_442_; lean_object* v___x_443_; 
v_index_441_ = lean_ctor_get(v___x_440_, 0);
lean_inc(v_index_441_);
lean_dec_ref_known(v___x_440_, 3);
v_size_442_ = lean_ctor_get(v___y_439_, 0);
lean_inc(v_size_442_);
v___x_443_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_439_, v_size_442_, v_index_441_, v_e_416_, v___y_438_);
lean_dec(v_index_441_);
v___y_423_ = v___y_437_;
v___y_424_ = v___x_443_;
goto v___jp_422_;
}
case 1:
{
lean_object* v_index_444_; 
v_index_444_ = lean_ctor_get(v___x_440_, 0);
lean_inc(v_index_444_);
lean_dec_ref_known(v___x_440_, 1);
v___y_428_ = v___y_439_;
v___y_429_ = v___y_437_;
v___y_430_ = v___y_438_;
v_i_431_ = v_index_444_;
goto v___jp_427_;
}
default: 
{
lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_445_ = lean_unsigned_to_nat(0u);
v___x_446_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_439_, v___x_445_);
if (lean_obj_tag(v___x_446_) == 0)
{
lean_object* v_index_447_; 
v_index_447_ = lean_ctor_get(v___x_446_, 0);
lean_inc(v_index_447_);
lean_dec_ref_known(v___x_446_, 1);
v___y_428_ = v___y_439_;
v___y_429_ = v___y_437_;
v___y_430_ = v___y_438_;
v_i_431_ = v_index_447_;
goto v___jp_427_;
}
else
{
lean_dec_ref(v___y_438_);
lean_dec_ref(v_e_416_);
v___y_423_ = v___y_437_;
v___y_424_ = v___y_439_;
goto v___jp_422_;
}
}
}
}
v___jp_448_:
{
lean_object* v_size_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
v_size_453_ = lean_ctor_get(v___y_451_, 0);
v___x_454_ = lean_unsigned_to_nat(1u);
v___x_455_ = lean_nat_add(v_size_453_, v___x_454_);
v___x_456_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_451_, v___x_455_, v_i_452_, v_e_416_, v___y_450_);
lean_dec(v_i_452_);
v___y_423_ = v___y_449_;
v___y_424_ = v___x_456_;
goto v___jp_422_;
}
v___jp_457_:
{
lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_461_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1___redArg(v___y_458_);
lean_dec_ref(v___y_458_);
v___x_462_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0___redArg(v___x_461_, v_e_416_);
switch(lean_obj_tag(v___x_462_))
{
case 0:
{
lean_object* v_index_463_; lean_object* v_size_464_; lean_object* v___x_465_; 
v_index_463_ = lean_ctor_get(v___x_462_, 0);
lean_inc(v_index_463_);
lean_dec_ref_known(v___x_462_, 3);
v_size_464_ = lean_ctor_get(v___x_461_, 0);
lean_inc(v_size_464_);
v___x_465_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_461_, v_size_464_, v_index_463_, v_e_416_, v___y_460_);
lean_dec(v_index_463_);
v___y_423_ = v___y_459_;
v___y_424_ = v___x_465_;
goto v___jp_422_;
}
case 1:
{
lean_object* v_index_466_; 
v_index_466_ = lean_ctor_get(v___x_462_, 0);
lean_inc(v_index_466_);
lean_dec_ref_known(v___x_462_, 1);
v___y_449_ = v___y_459_;
v___y_450_ = v___y_460_;
v___y_451_ = v___x_461_;
v_i_452_ = v_index_466_;
goto v___jp_448_;
}
default: 
{
lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_467_ = lean_unsigned_to_nat(0u);
v___x_468_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_461_, v___x_467_);
if (lean_obj_tag(v___x_468_) == 0)
{
lean_object* v_index_469_; 
v_index_469_ = lean_ctor_get(v___x_468_, 0);
lean_inc(v_index_469_);
lean_dec_ref_known(v___x_468_, 1);
v___y_449_ = v___y_459_;
v___y_450_ = v___y_460_;
v___y_451_ = v___x_461_;
v_i_452_ = v_index_469_;
goto v___jp_448_;
}
else
{
lean_dec_ref(v___y_460_);
lean_dec_ref(v_e_416_);
v___y_423_ = v___y_459_;
v___y_424_ = v___x_461_;
goto v___jp_422_;
}
}
}
}
v___jp_470_:
{
lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_473_ = lean_st_ref_take(v_a_417_);
v___x_474_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0___redArg(v___x_473_, v_e_416_);
switch(lean_obj_tag(v___x_474_))
{
case 0:
{
lean_object* v_index_475_; lean_object* v_size_476_; lean_object* v___x_477_; 
v_index_475_ = lean_ctor_get(v___x_474_, 0);
lean_inc(v_index_475_);
lean_dec_ref_known(v___x_474_, 3);
v_size_476_ = lean_ctor_get(v___x_473_, 0);
lean_inc(v_size_476_);
v___x_477_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_473_, v_size_476_, v_index_475_, v_e_416_, v_fst_472_);
lean_dec(v_index_475_);
v___y_423_ = v_a_471_;
v___y_424_ = v___x_477_;
goto v___jp_422_;
}
case 1:
{
lean_object* v_index_478_; lean_object* v_size_479_; lean_object* v_keyArray_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; uint8_t v___x_484_; 
v_index_478_ = lean_ctor_get(v___x_474_, 0);
lean_inc(v_index_478_);
lean_dec_ref_known(v___x_474_, 1);
v_size_479_ = lean_ctor_get(v___x_473_, 0);
lean_inc(v_size_479_);
v_keyArray_480_ = lean_ctor_get(v___x_473_, 1);
lean_inc_ref(v_keyArray_480_);
v___x_481_ = lean_unsigned_to_nat(1u);
v___x_482_ = lean_nat_add(v_size_479_, v___x_481_);
lean_dec(v_size_479_);
v___x_483_ = lean_array_get_size(v_keyArray_480_);
lean_dec_ref(v_keyArray_480_);
v___x_484_ = lean_nat_dec_lt(v___x_482_, v___x_483_);
if (v___x_484_ == 0)
{
lean_dec(v___x_482_);
lean_dec(v_index_478_);
v___y_458_ = v___x_473_;
v___y_459_ = v_a_471_;
v___y_460_ = v_fst_472_;
goto v___jp_457_;
}
else
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; uint8_t v___x_489_; 
v___x_485_ = lean_unsigned_to_nat(4u);
v___x_486_ = lean_nat_mul(v___x_482_, v___x_485_);
v___x_487_ = lean_unsigned_to_nat(3u);
v___x_488_ = lean_nat_mul(v___x_483_, v___x_487_);
v___x_489_ = lean_nat_dec_le(v___x_486_, v___x_488_);
lean_dec(v___x_488_);
lean_dec(v___x_486_);
if (v___x_489_ == 0)
{
lean_dec(v___x_482_);
lean_dec(v_index_478_);
v___y_458_ = v___x_473_;
v___y_459_ = v_a_471_;
v___y_460_ = v_fst_472_;
goto v___jp_457_;
}
else
{
lean_object* v___x_490_; 
v___x_490_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_473_, v___x_482_, v_index_478_, v_e_416_, v_fst_472_);
lean_dec(v_index_478_);
v___y_423_ = v_a_471_;
v___y_424_ = v___x_490_;
goto v___jp_422_;
}
}
}
default: 
{
lean_object* v_size_491_; lean_object* v_keyArray_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; uint8_t v___x_496_; 
v_size_491_ = lean_ctor_get(v___x_473_, 0);
lean_inc(v_size_491_);
v_keyArray_492_ = lean_ctor_get(v___x_473_, 1);
lean_inc_ref(v_keyArray_492_);
v___x_493_ = lean_unsigned_to_nat(1u);
v___x_494_ = lean_nat_add(v_size_491_, v___x_493_);
lean_dec(v_size_491_);
v___x_495_ = lean_array_get_size(v_keyArray_492_);
lean_dec_ref(v_keyArray_492_);
v___x_496_ = lean_nat_dec_lt(v___x_494_, v___x_495_);
if (v___x_496_ == 0)
{
lean_object* v___x_497_; 
lean_dec(v___x_494_);
v___x_497_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1___redArg(v___x_473_);
lean_dec(v___x_473_);
v___y_437_ = v_a_471_;
v___y_438_ = v_fst_472_;
v___y_439_ = v___x_497_;
goto v___jp_436_;
}
else
{
lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; uint8_t v___x_502_; 
v___x_498_ = lean_unsigned_to_nat(4u);
v___x_499_ = lean_nat_mul(v___x_494_, v___x_498_);
lean_dec(v___x_494_);
v___x_500_ = lean_unsigned_to_nat(3u);
v___x_501_ = lean_nat_mul(v___x_495_, v___x_500_);
v___x_502_ = lean_nat_dec_le(v___x_499_, v___x_501_);
lean_dec(v___x_501_);
lean_dec(v___x_499_);
if (v___x_502_ == 0)
{
lean_object* v___x_503_; 
v___x_503_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1___redArg(v___x_473_);
lean_dec(v___x_473_);
v___y_437_ = v_a_471_;
v___y_438_ = v_fst_472_;
v___y_439_ = v___x_503_;
goto v___jp_436_;
}
else
{
v___y_437_ = v_a_471_;
v___y_438_ = v_fst_472_;
v___y_439_ = v___x_473_;
goto v___jp_436_;
}
}
}
}
}
v___jp_504_:
{
if (lean_obj_tag(v___y_505_) == 0)
{
lean_object* v_a_506_; lean_object* v_fst_507_; 
v_a_506_ = lean_ctor_get(v___y_505_, 0);
lean_inc(v_a_506_);
lean_dec_ref_known(v___y_505_, 1);
v_fst_507_ = lean_ctor_get(v_a_506_, 0);
lean_inc(v_fst_507_);
v_a_471_ = v_a_506_;
v_fst_472_ = v_fst_507_;
goto v___jp_470_;
}
else
{
lean_dec_ref(v_e_416_);
return v___y_505_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___boxed(lean_object* v_e_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go(v_e_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_);
lean_dec(v_a_717_);
lean_dec_ref(v_a_716_);
lean_dec(v_a_714_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0(lean_object* v_00_u03b2_720_, lean_object* v_m_721_, lean_object* v_query_722_){
_start:
{
lean_object* v___x_723_; 
v___x_723_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0___redArg(v_m_721_, v_query_722_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0___boxed(lean_object* v_00_u03b2_724_, lean_object* v_m_725_, lean_object* v_query_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0(v_00_u03b2_724_, v_m_725_, v_query_726_);
lean_dec_ref(v_query_726_);
lean_dec_ref(v_m_725_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1(lean_object* v_00_u03b2_728_, lean_object* v_m_729_){
_start:
{
lean_object* v___x_730_; 
v___x_730_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1___redArg(v_m_729_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1___boxed(lean_object* v_00_u03b2_731_, lean_object* v_m_732_){
_start:
{
lean_object* v_res_733_; 
v_res_733_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1(v_00_u03b2_731_, v_m_732_);
lean_dec_ref(v_m_732_);
return v_res_733_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2(lean_object* v_00_u03b2_734_, lean_object* v_m_735_, lean_object* v_a_736_){
_start:
{
lean_object* v___x_737_; 
v___x_737_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2___redArg(v_m_735_, v_a_736_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2___boxed(lean_object* v_00_u03b2_738_, lean_object* v_m_739_, lean_object* v_a_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2(v_00_u03b2_738_, v_m_739_, v_a_740_);
lean_dec_ref(v_a_740_);
lean_dec_ref(v_m_739_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__0(lean_object* v_00_u03b2_742_, lean_object* v_m_743_, lean_object* v_query_744_, lean_object* v_x_745_, lean_object* v_x_746_, lean_object* v_x_747_, lean_object* v_x_748_){
_start:
{
lean_object* v___x_749_; 
v___x_749_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__0___redArg(v_m_743_, v_query_744_, v_x_745_, v_x_746_, v_x_747_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_750_, lean_object* v_m_751_, lean_object* v_query_752_, lean_object* v_x_753_, lean_object* v_x_754_, lean_object* v_x_755_, lean_object* v_x_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__0(v_00_u03b2_750_, v_m_751_, v_query_752_, v_x_753_, v_x_754_, v_x_755_, v_x_756_);
lean_dec_ref(v_query_752_);
lean_dec_ref(v_m_751_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1_spec__2(lean_object* v_00_u03b2_758_, lean_object* v_init_759_, lean_object* v_b_760_){
_start:
{
lean_object* v___x_761_; 
v___x_761_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1_spec__2___redArg(v_init_759_, v_b_760_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1_spec__2___boxed(lean_object* v_00_u03b2_762_, lean_object* v_init_763_, lean_object* v_b_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1_spec__2(v_00_u03b2_762_, v_init_763_, v_b_764_);
lean_dec_ref(v_b_764_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2_spec__4(lean_object* v_00_u03b2_766_, lean_object* v_m_767_, lean_object* v_query_768_){
_start:
{
lean_object* v___x_769_; 
v___x_769_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2_spec__4___redArg(v_m_767_, v_query_768_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2_spec__4___boxed(lean_object* v_00_u03b2_770_, lean_object* v_m_771_, lean_object* v_query_772_){
_start:
{
lean_object* v_res_773_; 
v_res_773_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2_spec__4(v_00_u03b2_770_, v_m_771_, v_query_772_);
lean_dec_ref(v_query_772_);
lean_dec_ref(v_m_771_);
return v_res_773_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_774_, lean_object* v_b_775_, lean_object* v_acc_776_, lean_object* v_i_777_){
_start:
{
lean_object* v___x_778_; 
v___x_778_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1_spec__2_spec__4___redArg(v_b_775_, v_acc_776_, v_i_777_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_779_, lean_object* v_b_780_, lean_object* v_acc_781_, lean_object* v_i_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1_spec__2_spec__4(v_00_u03b2_779_, v_b_780_, v_acc_781_, v_i_782_);
lean_dec_ref(v_b_780_);
return v_res_783_;
}
}
static lean_object* _init_l_Lean_Expr_resolveBinderNameHint___closed__0(void){
_start:
{
lean_object* v_cellCount_784_; lean_object* v___x_785_; 
v_cellCount_784_ = lean_unsigned_to_nat(16u);
v___x_785_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_784_);
return v___x_785_;
}
}
static lean_object* _init_l_Lean_Expr_resolveBinderNameHint___closed__1(void){
_start:
{
lean_object* v_cellCount_786_; lean_object* v___x_787_; 
v_cellCount_786_ = lean_unsigned_to_nat(16u);
v___x_787_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_786_);
return v___x_787_;
}
}
static lean_object* _init_l_Lean_Expr_resolveBinderNameHint___closed__2(void){
_start:
{
lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_788_ = lean_obj_once(&l_Lean_Expr_resolveBinderNameHint___closed__1, &l_Lean_Expr_resolveBinderNameHint___closed__1_once, _init_l_Lean_Expr_resolveBinderNameHint___closed__1);
v___x_789_ = lean_obj_once(&l_Lean_Expr_resolveBinderNameHint___closed__0, &l_Lean_Expr_resolveBinderNameHint___closed__0_once, _init_l_Lean_Expr_resolveBinderNameHint___closed__0);
v___x_790_ = lean_unsigned_to_nat(0u);
v___x_791_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_791_, 0, v___x_790_);
lean_ctor_set(v___x_791_, 1, v___x_789_);
lean_ctor_set(v___x_791_, 2, v___x_788_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_resolveBinderNameHint(lean_object* v_e_794_, lean_object* v_a_795_, lean_object* v_a_796_){
_start:
{
lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_798_ = lean_obj_once(&l_Lean_Expr_resolveBinderNameHint___closed__2, &l_Lean_Expr_resolveBinderNameHint___closed__2_once, _init_l_Lean_Expr_resolveBinderNameHint___closed__2);
v___x_799_ = lean_st_mk_ref(v___x_798_);
v___x_800_ = ((lean_object*)(l_Lean_Expr_resolveBinderNameHint___closed__3));
v___x_801_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go(v_e_794_, v___x_799_, v___x_800_, v_a_795_, v_a_796_);
if (lean_obj_tag(v___x_801_) == 0)
{
lean_object* v_a_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_811_; 
v_a_802_ = lean_ctor_get(v___x_801_, 0);
v_isSharedCheck_811_ = !lean_is_exclusive(v___x_801_);
if (v_isSharedCheck_811_ == 0)
{
v___x_804_ = v___x_801_;
v_isShared_805_ = v_isSharedCheck_811_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_a_802_);
lean_dec(v___x_801_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_811_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v_fst_806_; lean_object* v___x_807_; lean_object* v___x_809_; 
v_fst_806_ = lean_ctor_get(v_a_802_, 0);
lean_inc(v_fst_806_);
lean_dec(v_a_802_);
v___x_807_ = lean_st_ref_get(v___x_799_);
lean_dec(v___x_799_);
lean_dec(v___x_807_);
if (v_isShared_805_ == 0)
{
lean_ctor_set(v___x_804_, 0, v_fst_806_);
v___x_809_ = v___x_804_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_fst_806_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
}
else
{
lean_object* v_a_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_819_; 
lean_dec(v___x_799_);
v_a_812_ = lean_ctor_get(v___x_801_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_801_);
if (v_isSharedCheck_819_ == 0)
{
v___x_814_ = v___x_801_;
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_a_812_);
lean_dec(v___x_801_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_817_; 
if (v_isShared_815_ == 0)
{
v___x_817_ = v___x_814_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_a_812_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_resolveBinderNameHint___boxed(lean_object* v_e_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l_Lean_Expr_resolveBinderNameHint(v_e_820_, v_a_821_, v_a_822_);
lean_dec(v_a_822_);
lean_dec_ref(v_a_821_);
return v_res_824_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_BinderNameHint(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_BinderNameHint(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_BinderNameHint(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_BinderNameHint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_BinderNameHint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_BinderNameHint(builtin);
}
#ifdef __cplusplus
}
#endif
