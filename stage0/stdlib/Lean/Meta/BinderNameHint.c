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
uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_ExprStructEq_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Array_instInhabited(lean_object*);
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
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
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
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2___closed__0;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2___closed__2_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ExprStructEq_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2___closed__3 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2___closed__3_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ExprStructEq_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2___closed__4 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__1_spec__3_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 71, .m_capacity = 71, .m_length = 70, .m_data = "_private.Lean.Meta.BinderNameHint.0.Lean.Expr.resolveBinderNameHint.go"};
static const lean_object* l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___closed__0_value;
static const lean_string_object l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "assertion violation: xs.size > bidx\n          "};
static const lean_object* l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___closed__1 = (const lean_object*)&l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__1_spec__3_spec__5(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Expr_resolveBinderNameHint___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_resolveBinderNameHint___closed__0;
static lean_once_cell_t l_Lean_Expr_resolveBinderNameHint___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_resolveBinderNameHint___closed__1;
static const lean_array_object l_Lean_Expr_resolveBinderNameHint___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Expr_resolveBinderNameHint___closed__2 = (const lean_object*)&l_Lean_Expr_resolveBinderNameHint___closed__2_value;
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
lean_dec_ref(v___x_13_);
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
lean_dec_ref(v___x_26_);
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
static lean_object* _init_l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2___closed__0(void){
_start:
{
lean_object* v___x_133_; 
v___x_133_ = l_instMonadEIO(lean_box(0));
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2(lean_object* v_msg_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v_toApplicative_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_191_; 
v___x_144_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2___closed__0, &l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2___closed__0);
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
v___f_157_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2___closed__1));
v___f_158_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2___closed__2));
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
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___f_172_; lean_object* v___f_173_; lean_object* v___f_174_; lean_object* v___f_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_13989__overap_185_; lean_object* v___x_186_; 
v___x_169_ = lean_box(0);
v___x_170_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2___closed__3));
v___x_171_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2___closed__4));
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
v___x_13989__overap_185_ = lean_panic_fn_borrowed(v___x_184_, v_msg_138_);
lean_dec(v___x_184_);
lean_inc(v___y_142_);
lean_inc_ref(v___y_141_);
lean_inc(v___y_139_);
v___x_186_ = lean_apply_5(v___x_13989__overap_185_, v___y_139_, v___y_140_, v___y_141_, v___y_142_, lean_box(0));
return v___x_186_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2___boxed(lean_object* v_msg_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2(v_msg_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_);
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
uint8_t v_binderInfo_14512__boxed_242_; lean_object* v_res_243_; 
v_binderInfo_14512__boxed_242_ = lean_unbox(v_binderInfo_236_);
v_res_243_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___lam__1(v___f_231_, v_bidx_232_, v_n_233_, v_binderType_234_, v_body_235_, v_binderInfo_14512__boxed_242_, v___y_237_, v___y_238_, v___y_239_, v___y_240_);
lean_dec(v___y_240_);
lean_dec_ref(v___y_239_);
lean_dec(v___y_237_);
lean_dec_ref(v_body_235_);
lean_dec_ref(v_binderType_234_);
lean_dec(v_bidx_232_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__1_spec__3_spec__5___redArg(lean_object* v_x_244_, lean_object* v_x_245_){
_start:
{
if (lean_obj_tag(v_x_245_) == 0)
{
return v_x_244_;
}
else
{
lean_object* v_key_246_; lean_object* v_value_247_; lean_object* v_tail_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_271_; 
v_key_246_ = lean_ctor_get(v_x_245_, 0);
v_value_247_ = lean_ctor_get(v_x_245_, 1);
v_tail_248_ = lean_ctor_get(v_x_245_, 2);
v_isSharedCheck_271_ = !lean_is_exclusive(v_x_245_);
if (v_isSharedCheck_271_ == 0)
{
v___x_250_ = v_x_245_;
v_isShared_251_ = v_isSharedCheck_271_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_tail_248_);
lean_inc(v_value_247_);
lean_inc(v_key_246_);
lean_dec(v_x_245_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_271_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
lean_object* v___x_252_; uint64_t v___x_253_; uint64_t v___x_254_; uint64_t v___x_255_; uint64_t v_fold_256_; uint64_t v___x_257_; uint64_t v___x_258_; uint64_t v___x_259_; size_t v___x_260_; size_t v___x_261_; size_t v___x_262_; size_t v___x_263_; size_t v___x_264_; lean_object* v___x_265_; lean_object* v___x_267_; 
v___x_252_ = lean_array_get_size(v_x_244_);
v___x_253_ = l_Lean_ExprStructEq_hash(v_key_246_);
v___x_254_ = 32ULL;
v___x_255_ = lean_uint64_shift_right(v___x_253_, v___x_254_);
v_fold_256_ = lean_uint64_xor(v___x_253_, v___x_255_);
v___x_257_ = 16ULL;
v___x_258_ = lean_uint64_shift_right(v_fold_256_, v___x_257_);
v___x_259_ = lean_uint64_xor(v_fold_256_, v___x_258_);
v___x_260_ = lean_uint64_to_usize(v___x_259_);
v___x_261_ = lean_usize_of_nat(v___x_252_);
v___x_262_ = ((size_t)1ULL);
v___x_263_ = lean_usize_sub(v___x_261_, v___x_262_);
v___x_264_ = lean_usize_land(v___x_260_, v___x_263_);
v___x_265_ = lean_array_uget_borrowed(v_x_244_, v___x_264_);
lean_inc(v___x_265_);
if (v_isShared_251_ == 0)
{
lean_ctor_set(v___x_250_, 2, v___x_265_);
v___x_267_ = v___x_250_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v_key_246_);
lean_ctor_set(v_reuseFailAlloc_270_, 1, v_value_247_);
lean_ctor_set(v_reuseFailAlloc_270_, 2, v___x_265_);
v___x_267_ = v_reuseFailAlloc_270_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
lean_object* v___x_268_; 
v___x_268_ = lean_array_uset(v_x_244_, v___x_264_, v___x_267_);
v_x_244_ = v___x_268_;
v_x_245_ = v_tail_248_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__1_spec__3___redArg(lean_object* v_i_272_, lean_object* v_source_273_, lean_object* v_target_274_){
_start:
{
lean_object* v___x_275_; uint8_t v___x_276_; 
v___x_275_ = lean_array_get_size(v_source_273_);
v___x_276_ = lean_nat_dec_lt(v_i_272_, v___x_275_);
if (v___x_276_ == 0)
{
lean_dec_ref(v_source_273_);
lean_dec(v_i_272_);
return v_target_274_;
}
else
{
lean_object* v_es_277_; lean_object* v___x_278_; lean_object* v_source_279_; lean_object* v_target_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v_es_277_ = lean_array_fget(v_source_273_, v_i_272_);
v___x_278_ = lean_box(0);
v_source_279_ = lean_array_fset(v_source_273_, v_i_272_, v___x_278_);
v_target_280_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__1_spec__3_spec__5___redArg(v_target_274_, v_es_277_);
v___x_281_ = lean_unsigned_to_nat(1u);
v___x_282_ = lean_nat_add(v_i_272_, v___x_281_);
lean_dec(v_i_272_);
v_i_272_ = v___x_282_;
v_source_273_ = v_source_279_;
v_target_274_ = v_target_280_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__1___redArg(lean_object* v_data_284_){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v_nbuckets_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_285_ = lean_array_get_size(v_data_284_);
v___x_286_ = lean_unsigned_to_nat(2u);
v_nbuckets_287_ = lean_nat_mul(v___x_285_, v___x_286_);
v___x_288_ = lean_unsigned_to_nat(0u);
v___x_289_ = lean_box(0);
v___x_290_ = lean_mk_array(v_nbuckets_287_, v___x_289_);
v___x_291_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__1_spec__3___redArg(v___x_288_, v_data_284_, v___x_290_);
return v___x_291_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__0___redArg(lean_object* v_a_292_, lean_object* v_x_293_){
_start:
{
if (lean_obj_tag(v_x_293_) == 0)
{
uint8_t v___x_294_; 
v___x_294_ = 0;
return v___x_294_;
}
else
{
lean_object* v_key_295_; lean_object* v_tail_296_; uint8_t v___x_297_; 
v_key_295_ = lean_ctor_get(v_x_293_, 0);
v_tail_296_ = lean_ctor_get(v_x_293_, 2);
v___x_297_ = l_Lean_ExprStructEq_beq(v_key_295_, v_a_292_);
if (v___x_297_ == 0)
{
v_x_293_ = v_tail_296_;
goto _start;
}
else
{
return v___x_297_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__0___redArg___boxed(lean_object* v_a_299_, lean_object* v_x_300_){
_start:
{
uint8_t v_res_301_; lean_object* v_r_302_; 
v_res_301_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__0___redArg(v_a_299_, v_x_300_);
lean_dec(v_x_300_);
lean_dec_ref(v_a_299_);
v_r_302_ = lean_box(v_res_301_);
return v_r_302_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__2___redArg(lean_object* v_a_303_, lean_object* v_b_304_, lean_object* v_x_305_){
_start:
{
if (lean_obj_tag(v_x_305_) == 0)
{
lean_dec(v_b_304_);
lean_dec_ref(v_a_303_);
return v_x_305_;
}
else
{
lean_object* v_key_306_; lean_object* v_value_307_; lean_object* v_tail_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_320_; 
v_key_306_ = lean_ctor_get(v_x_305_, 0);
v_value_307_ = lean_ctor_get(v_x_305_, 1);
v_tail_308_ = lean_ctor_get(v_x_305_, 2);
v_isSharedCheck_320_ = !lean_is_exclusive(v_x_305_);
if (v_isSharedCheck_320_ == 0)
{
v___x_310_ = v_x_305_;
v_isShared_311_ = v_isSharedCheck_320_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_tail_308_);
lean_inc(v_value_307_);
lean_inc(v_key_306_);
lean_dec(v_x_305_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_320_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
uint8_t v___x_312_; 
v___x_312_ = l_Lean_ExprStructEq_beq(v_key_306_, v_a_303_);
if (v___x_312_ == 0)
{
lean_object* v___x_313_; lean_object* v___x_315_; 
v___x_313_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__2___redArg(v_a_303_, v_b_304_, v_tail_308_);
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 2, v___x_313_);
v___x_315_ = v___x_310_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_key_306_);
lean_ctor_set(v_reuseFailAlloc_316_, 1, v_value_307_);
lean_ctor_set(v_reuseFailAlloc_316_, 2, v___x_313_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
return v___x_315_;
}
}
else
{
lean_object* v___x_318_; 
lean_dec(v_value_307_);
lean_dec(v_key_306_);
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 1, v_b_304_);
lean_ctor_set(v___x_310_, 0, v_a_303_);
v___x_318_ = v___x_310_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v_a_303_);
lean_ctor_set(v_reuseFailAlloc_319_, 1, v_b_304_);
lean_ctor_set(v_reuseFailAlloc_319_, 2, v_tail_308_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0___redArg(lean_object* v_m_321_, lean_object* v_a_322_, lean_object* v_b_323_){
_start:
{
lean_object* v_size_324_; lean_object* v_buckets_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_368_; 
v_size_324_ = lean_ctor_get(v_m_321_, 0);
v_buckets_325_ = lean_ctor_get(v_m_321_, 1);
v_isSharedCheck_368_ = !lean_is_exclusive(v_m_321_);
if (v_isSharedCheck_368_ == 0)
{
v___x_327_ = v_m_321_;
v_isShared_328_ = v_isSharedCheck_368_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_buckets_325_);
lean_inc(v_size_324_);
lean_dec(v_m_321_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_368_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_329_; uint64_t v___x_330_; uint64_t v___x_331_; uint64_t v___x_332_; uint64_t v_fold_333_; uint64_t v___x_334_; uint64_t v___x_335_; uint64_t v___x_336_; size_t v___x_337_; size_t v___x_338_; size_t v___x_339_; size_t v___x_340_; size_t v___x_341_; lean_object* v_bkt_342_; uint8_t v___x_343_; 
v___x_329_ = lean_array_get_size(v_buckets_325_);
v___x_330_ = l_Lean_ExprStructEq_hash(v_a_322_);
v___x_331_ = 32ULL;
v___x_332_ = lean_uint64_shift_right(v___x_330_, v___x_331_);
v_fold_333_ = lean_uint64_xor(v___x_330_, v___x_332_);
v___x_334_ = 16ULL;
v___x_335_ = lean_uint64_shift_right(v_fold_333_, v___x_334_);
v___x_336_ = lean_uint64_xor(v_fold_333_, v___x_335_);
v___x_337_ = lean_uint64_to_usize(v___x_336_);
v___x_338_ = lean_usize_of_nat(v___x_329_);
v___x_339_ = ((size_t)1ULL);
v___x_340_ = lean_usize_sub(v___x_338_, v___x_339_);
v___x_341_ = lean_usize_land(v___x_337_, v___x_340_);
v_bkt_342_ = lean_array_uget_borrowed(v_buckets_325_, v___x_341_);
v___x_343_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__0___redArg(v_a_322_, v_bkt_342_);
if (v___x_343_ == 0)
{
lean_object* v___x_344_; lean_object* v_size_x27_345_; lean_object* v___x_346_; lean_object* v_buckets_x27_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; uint8_t v___x_353_; 
v___x_344_ = lean_unsigned_to_nat(1u);
v_size_x27_345_ = lean_nat_add(v_size_324_, v___x_344_);
lean_dec(v_size_324_);
lean_inc(v_bkt_342_);
v___x_346_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_346_, 0, v_a_322_);
lean_ctor_set(v___x_346_, 1, v_b_323_);
lean_ctor_set(v___x_346_, 2, v_bkt_342_);
v_buckets_x27_347_ = lean_array_uset(v_buckets_325_, v___x_341_, v___x_346_);
v___x_348_ = lean_unsigned_to_nat(4u);
v___x_349_ = lean_nat_mul(v_size_x27_345_, v___x_348_);
v___x_350_ = lean_unsigned_to_nat(3u);
v___x_351_ = lean_nat_div(v___x_349_, v___x_350_);
lean_dec(v___x_349_);
v___x_352_ = lean_array_get_size(v_buckets_x27_347_);
v___x_353_ = lean_nat_dec_le(v___x_351_, v___x_352_);
lean_dec(v___x_351_);
if (v___x_353_ == 0)
{
lean_object* v_val_354_; lean_object* v___x_356_; 
v_val_354_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__1___redArg(v_buckets_x27_347_);
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 1, v_val_354_);
lean_ctor_set(v___x_327_, 0, v_size_x27_345_);
v___x_356_ = v___x_327_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_size_x27_345_);
lean_ctor_set(v_reuseFailAlloc_357_, 1, v_val_354_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
else
{
lean_object* v___x_359_; 
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 1, v_buckets_x27_347_);
lean_ctor_set(v___x_327_, 0, v_size_x27_345_);
v___x_359_ = v___x_327_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v_size_x27_345_);
lean_ctor_set(v_reuseFailAlloc_360_, 1, v_buckets_x27_347_);
v___x_359_ = v_reuseFailAlloc_360_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
return v___x_359_;
}
}
}
else
{
lean_object* v___x_361_; lean_object* v_buckets_x27_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_366_; 
lean_inc(v_bkt_342_);
v___x_361_ = lean_box(0);
v_buckets_x27_362_ = lean_array_uset(v_buckets_325_, v___x_341_, v___x_361_);
v___x_363_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__2___redArg(v_a_322_, v_b_323_, v_bkt_342_);
v___x_364_ = lean_array_uset(v_buckets_x27_362_, v___x_341_, v___x_363_);
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 1, v___x_364_);
v___x_366_ = v___x_327_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v_size_324_);
lean_ctor_set(v_reuseFailAlloc_367_, 1, v___x_364_);
v___x_366_ = v_reuseFailAlloc_367_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
return v___x_366_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1_spec__4___redArg(lean_object* v_a_369_, lean_object* v_x_370_){
_start:
{
if (lean_obj_tag(v_x_370_) == 0)
{
lean_object* v___x_371_; 
v___x_371_ = lean_box(0);
return v___x_371_;
}
else
{
lean_object* v_key_372_; lean_object* v_value_373_; lean_object* v_tail_374_; uint8_t v___x_375_; 
v_key_372_ = lean_ctor_get(v_x_370_, 0);
v_value_373_ = lean_ctor_get(v_x_370_, 1);
v_tail_374_ = lean_ctor_get(v_x_370_, 2);
v___x_375_ = l_Lean_ExprStructEq_beq(v_key_372_, v_a_369_);
if (v___x_375_ == 0)
{
v_x_370_ = v_tail_374_;
goto _start;
}
else
{
lean_object* v___x_377_; 
lean_inc(v_value_373_);
v___x_377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_377_, 0, v_value_373_);
return v___x_377_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1_spec__4___redArg___boxed(lean_object* v_a_378_, lean_object* v_x_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1_spec__4___redArg(v_a_378_, v_x_379_);
lean_dec(v_x_379_);
lean_dec_ref(v_a_378_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1___redArg(lean_object* v_m_381_, lean_object* v_a_382_){
_start:
{
lean_object* v_buckets_383_; lean_object* v___x_384_; uint64_t v___x_385_; uint64_t v___x_386_; uint64_t v___x_387_; uint64_t v_fold_388_; uint64_t v___x_389_; uint64_t v___x_390_; uint64_t v___x_391_; size_t v___x_392_; size_t v___x_393_; size_t v___x_394_; size_t v___x_395_; size_t v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v_buckets_383_ = lean_ctor_get(v_m_381_, 1);
v___x_384_ = lean_array_get_size(v_buckets_383_);
v___x_385_ = l_Lean_ExprStructEq_hash(v_a_382_);
v___x_386_ = 32ULL;
v___x_387_ = lean_uint64_shift_right(v___x_385_, v___x_386_);
v_fold_388_ = lean_uint64_xor(v___x_385_, v___x_387_);
v___x_389_ = 16ULL;
v___x_390_ = lean_uint64_shift_right(v_fold_388_, v___x_389_);
v___x_391_ = lean_uint64_xor(v_fold_388_, v___x_390_);
v___x_392_ = lean_uint64_to_usize(v___x_391_);
v___x_393_ = lean_usize_of_nat(v___x_384_);
v___x_394_ = ((size_t)1ULL);
v___x_395_ = lean_usize_sub(v___x_393_, v___x_394_);
v___x_396_ = lean_usize_land(v___x_392_, v___x_395_);
v___x_397_ = lean_array_uget_borrowed(v_buckets_383_, v___x_396_);
v___x_398_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1_spec__4___redArg(v_a_382_, v___x_397_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1___redArg___boxed(lean_object* v_m_399_, lean_object* v_a_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1___redArg(v_m_399_, v_a_400_);
lean_dec_ref(v_a_400_);
lean_dec_ref(v_m_399_);
return v_res_401_;
}
}
static lean_object* _init_l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___closed__2(void){
_start:
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_404_ = ((lean_object*)(l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___closed__1));
v___x_405_ = lean_unsigned_to_nat(10u);
v___x_406_ = lean_unsigned_to_nat(72u);
v___x_407_ = ((lean_object*)(l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___closed__0));
v___x_408_ = ((lean_object*)(l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope___closed__0));
v___x_409_ = l_mkPanicMessageWithDecl(v___x_408_, v___x_407_, v___x_406_, v___x_405_, v___x_404_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go(lean_object* v_e_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_){
_start:
{
lean_object* v_a_417_; lean_object* v_fst_418_; lean_object* v___y_424_; lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_427_ = lean_st_ref_get(v_a_411_);
v___x_428_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1___redArg(v___x_427_, v_e_410_);
lean_dec(v___x_427_);
if (lean_obj_tag(v___x_428_) == 0)
{
lean_object* v___x_429_; lean_object* v___x_430_; uint8_t v___x_431_; 
v___x_429_ = ((lean_object*)(l_Lean_Expr_hasBinderNameHint___lam__0___closed__1));
v___x_430_ = lean_unsigned_to_nat(6u);
v___x_431_ = l_Lean_Expr_isAppOfArity(v_e_410_, v___x_429_, v___x_430_);
if (v___x_431_ == 0)
{
switch(lean_obj_tag(v_e_410_))
{
case 7:
{
lean_object* v_binderName_432_; lean_object* v_binderType_433_; lean_object* v_body_434_; uint8_t v_binderInfo_435_; lean_object* v___x_436_; 
v_binderName_432_ = lean_ctor_get(v_e_410_, 0);
v_binderType_433_ = lean_ctor_get(v_e_410_, 1);
v_body_434_ = lean_ctor_get(v_e_410_, 2);
v_binderInfo_435_ = lean_ctor_get_uint8(v_e_410_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_433_);
v___x_436_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go(v_binderType_433_, v_a_411_, v_a_412_, v_a_413_, v_a_414_);
if (lean_obj_tag(v___x_436_) == 0)
{
lean_object* v_a_437_; lean_object* v_fst_438_; lean_object* v_snd_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
v_a_437_ = lean_ctor_get(v___x_436_, 0);
lean_inc(v_a_437_);
lean_dec_ref(v___x_436_);
v_fst_438_ = lean_ctor_get(v_a_437_, 0);
lean_inc(v_fst_438_);
v_snd_439_ = lean_ctor_get(v_a_437_, 1);
lean_inc(v_snd_439_);
lean_dec(v_a_437_);
lean_inc(v_binderName_432_);
v___x_440_ = lean_array_push(v_snd_439_, v_binderName_432_);
lean_inc_ref(v_body_434_);
v___x_441_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go(v_body_434_, v_a_411_, v___x_440_, v_a_413_, v_a_414_);
if (lean_obj_tag(v___x_441_) == 0)
{
lean_object* v_a_442_; lean_object* v_fst_443_; lean_object* v_snd_444_; lean_object* v___x_445_; lean_object* v_fst_446_; lean_object* v_snd_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_455_; 
v_a_442_ = lean_ctor_get(v___x_441_, 0);
lean_inc(v_a_442_);
lean_dec_ref(v___x_441_);
v_fst_443_ = lean_ctor_get(v_a_442_, 0);
lean_inc(v_fst_443_);
v_snd_444_ = lean_ctor_get(v_a_442_, 1);
lean_inc(v_snd_444_);
lean_dec(v_a_442_);
v___x_445_ = l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope(v_snd_444_);
v_fst_446_ = lean_ctor_get(v___x_445_, 0);
v_snd_447_ = lean_ctor_get(v___x_445_, 1);
v_isSharedCheck_455_ = !lean_is_exclusive(v___x_445_);
if (v_isSharedCheck_455_ == 0)
{
v___x_449_ = v___x_445_;
v_isShared_450_ = v_isSharedCheck_455_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_snd_447_);
lean_inc(v_fst_446_);
lean_dec(v___x_445_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_455_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_451_; lean_object* v___x_453_; 
v___x_451_ = l_Lean_Expr_forallE___override(v_fst_446_, v_fst_438_, v_fst_443_, v_binderInfo_435_);
lean_inc_ref(v___x_451_);
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 0, v___x_451_);
v___x_453_ = v___x_449_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v___x_451_);
lean_ctor_set(v_reuseFailAlloc_454_, 1, v_snd_447_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
v_a_417_ = v___x_453_;
v_fst_418_ = v___x_451_;
goto v___jp_416_;
}
}
}
else
{
lean_dec(v_fst_438_);
v___y_424_ = v___x_441_;
goto v___jp_423_;
}
}
else
{
v___y_424_ = v___x_436_;
goto v___jp_423_;
}
}
case 6:
{
lean_object* v_binderName_456_; lean_object* v_binderType_457_; lean_object* v_body_458_; uint8_t v_binderInfo_459_; lean_object* v___x_460_; 
v_binderName_456_ = lean_ctor_get(v_e_410_, 0);
v_binderType_457_ = lean_ctor_get(v_e_410_, 1);
v_body_458_ = lean_ctor_get(v_e_410_, 2);
v_binderInfo_459_ = lean_ctor_get_uint8(v_e_410_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_457_);
v___x_460_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go(v_binderType_457_, v_a_411_, v_a_412_, v_a_413_, v_a_414_);
if (lean_obj_tag(v___x_460_) == 0)
{
lean_object* v_a_461_; lean_object* v_fst_462_; lean_object* v_snd_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
v_a_461_ = lean_ctor_get(v___x_460_, 0);
lean_inc(v_a_461_);
lean_dec_ref(v___x_460_);
v_fst_462_ = lean_ctor_get(v_a_461_, 0);
lean_inc(v_fst_462_);
v_snd_463_ = lean_ctor_get(v_a_461_, 1);
lean_inc(v_snd_463_);
lean_dec(v_a_461_);
lean_inc(v_binderName_456_);
v___x_464_ = lean_array_push(v_snd_463_, v_binderName_456_);
lean_inc_ref(v_body_458_);
v___x_465_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go(v_body_458_, v_a_411_, v___x_464_, v_a_413_, v_a_414_);
if (lean_obj_tag(v___x_465_) == 0)
{
lean_object* v_a_466_; lean_object* v_fst_467_; lean_object* v_snd_468_; lean_object* v___x_469_; lean_object* v_fst_470_; lean_object* v_snd_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_479_; 
v_a_466_ = lean_ctor_get(v___x_465_, 0);
lean_inc(v_a_466_);
lean_dec_ref(v___x_465_);
v_fst_467_ = lean_ctor_get(v_a_466_, 0);
lean_inc(v_fst_467_);
v_snd_468_ = lean_ctor_get(v_a_466_, 1);
lean_inc(v_snd_468_);
lean_dec(v_a_466_);
v___x_469_ = l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope(v_snd_468_);
v_fst_470_ = lean_ctor_get(v___x_469_, 0);
v_snd_471_ = lean_ctor_get(v___x_469_, 1);
v_isSharedCheck_479_ = !lean_is_exclusive(v___x_469_);
if (v_isSharedCheck_479_ == 0)
{
v___x_473_ = v___x_469_;
v_isShared_474_ = v_isSharedCheck_479_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_snd_471_);
lean_inc(v_fst_470_);
lean_dec(v___x_469_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_479_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_475_; lean_object* v___x_477_; 
v___x_475_ = l_Lean_Expr_lam___override(v_fst_470_, v_fst_462_, v_fst_467_, v_binderInfo_459_);
lean_inc_ref(v___x_475_);
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 0, v___x_475_);
v___x_477_ = v___x_473_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v___x_475_);
lean_ctor_set(v_reuseFailAlloc_478_, 1, v_snd_471_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
v_a_417_ = v___x_477_;
v_fst_418_ = v___x_475_;
goto v___jp_416_;
}
}
}
else
{
lean_dec(v_fst_462_);
v___y_424_ = v___x_465_;
goto v___jp_423_;
}
}
else
{
v___y_424_ = v___x_460_;
goto v___jp_423_;
}
}
case 8:
{
lean_object* v_declName_480_; lean_object* v_type_481_; lean_object* v_value_482_; lean_object* v_body_483_; uint8_t v_nondep_484_; lean_object* v___x_485_; 
v_declName_480_ = lean_ctor_get(v_e_410_, 0);
v_type_481_ = lean_ctor_get(v_e_410_, 1);
v_value_482_ = lean_ctor_get(v_e_410_, 2);
v_body_483_ = lean_ctor_get(v_e_410_, 3);
v_nondep_484_ = lean_ctor_get_uint8(v_e_410_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_481_);
v___x_485_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go(v_type_481_, v_a_411_, v_a_412_, v_a_413_, v_a_414_);
if (lean_obj_tag(v___x_485_) == 0)
{
lean_object* v_a_486_; lean_object* v_fst_487_; lean_object* v_snd_488_; lean_object* v___x_489_; 
v_a_486_ = lean_ctor_get(v___x_485_, 0);
lean_inc(v_a_486_);
lean_dec_ref(v___x_485_);
v_fst_487_ = lean_ctor_get(v_a_486_, 0);
lean_inc(v_fst_487_);
v_snd_488_ = lean_ctor_get(v_a_486_, 1);
lean_inc(v_snd_488_);
lean_dec(v_a_486_);
lean_inc_ref(v_value_482_);
v___x_489_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go(v_value_482_, v_a_411_, v_snd_488_, v_a_413_, v_a_414_);
if (lean_obj_tag(v___x_489_) == 0)
{
lean_object* v_a_490_; lean_object* v_fst_491_; lean_object* v_snd_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v_a_490_ = lean_ctor_get(v___x_489_, 0);
lean_inc(v_a_490_);
lean_dec_ref(v___x_489_);
v_fst_491_ = lean_ctor_get(v_a_490_, 0);
lean_inc(v_fst_491_);
v_snd_492_ = lean_ctor_get(v_a_490_, 1);
lean_inc(v_snd_492_);
lean_dec(v_a_490_);
lean_inc(v_declName_480_);
v___x_493_ = lean_array_push(v_snd_492_, v_declName_480_);
lean_inc_ref(v_body_483_);
v___x_494_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go(v_body_483_, v_a_411_, v___x_493_, v_a_413_, v_a_414_);
if (lean_obj_tag(v___x_494_) == 0)
{
lean_object* v_a_495_; lean_object* v_fst_496_; lean_object* v_snd_497_; lean_object* v___x_498_; lean_object* v_fst_499_; lean_object* v_snd_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_508_; 
v_a_495_ = lean_ctor_get(v___x_494_, 0);
lean_inc(v_a_495_);
lean_dec_ref(v___x_494_);
v_fst_496_ = lean_ctor_get(v_a_495_, 0);
lean_inc(v_fst_496_);
v_snd_497_ = lean_ctor_get(v_a_495_, 1);
lean_inc(v_snd_497_);
lean_dec(v_a_495_);
v___x_498_ = l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope(v_snd_497_);
v_fst_499_ = lean_ctor_get(v___x_498_, 0);
v_snd_500_ = lean_ctor_get(v___x_498_, 1);
v_isSharedCheck_508_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_508_ == 0)
{
v___x_502_ = v___x_498_;
v_isShared_503_ = v_isSharedCheck_508_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_snd_500_);
lean_inc(v_fst_499_);
lean_dec(v___x_498_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_508_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v___x_504_; lean_object* v___x_506_; 
v___x_504_ = l_Lean_Expr_letE___override(v_fst_499_, v_fst_487_, v_fst_491_, v_fst_496_, v_nondep_484_);
lean_inc_ref(v___x_504_);
if (v_isShared_503_ == 0)
{
lean_ctor_set(v___x_502_, 0, v___x_504_);
v___x_506_ = v___x_502_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v___x_504_);
lean_ctor_set(v_reuseFailAlloc_507_, 1, v_snd_500_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
v_a_417_ = v___x_506_;
v_fst_418_ = v___x_504_;
goto v___jp_416_;
}
}
}
else
{
lean_dec(v_fst_491_);
lean_dec(v_fst_487_);
v___y_424_ = v___x_494_;
goto v___jp_423_;
}
}
else
{
lean_dec(v_fst_487_);
v___y_424_ = v___x_489_;
goto v___jp_423_;
}
}
else
{
v___y_424_ = v___x_485_;
goto v___jp_423_;
}
}
case 5:
{
lean_object* v_fn_509_; lean_object* v_arg_510_; lean_object* v___x_511_; 
v_fn_509_ = lean_ctor_get(v_e_410_, 0);
v_arg_510_ = lean_ctor_get(v_e_410_, 1);
lean_inc_ref(v_fn_509_);
v___x_511_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go(v_fn_509_, v_a_411_, v_a_412_, v_a_413_, v_a_414_);
if (lean_obj_tag(v___x_511_) == 0)
{
lean_object* v_a_512_; lean_object* v_fst_513_; lean_object* v_snd_514_; lean_object* v___x_515_; 
v_a_512_ = lean_ctor_get(v___x_511_, 0);
lean_inc(v_a_512_);
lean_dec_ref(v___x_511_);
v_fst_513_ = lean_ctor_get(v_a_512_, 0);
lean_inc(v_fst_513_);
v_snd_514_ = lean_ctor_get(v_a_512_, 1);
lean_inc(v_snd_514_);
lean_dec(v_a_512_);
lean_inc_ref(v_arg_510_);
v___x_515_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go(v_arg_510_, v_a_411_, v_snd_514_, v_a_413_, v_a_414_);
if (lean_obj_tag(v___x_515_) == 0)
{
lean_object* v_a_516_; lean_object* v_fst_517_; lean_object* v_snd_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_536_; 
v_a_516_ = lean_ctor_get(v___x_515_, 0);
lean_inc(v_a_516_);
lean_dec_ref(v___x_515_);
v_fst_517_ = lean_ctor_get(v_a_516_, 0);
v_snd_518_ = lean_ctor_get(v_a_516_, 1);
v_isSharedCheck_536_ = !lean_is_exclusive(v_a_516_);
if (v_isSharedCheck_536_ == 0)
{
v___x_520_ = v_a_516_;
v_isShared_521_ = v_isSharedCheck_536_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_snd_518_);
lean_inc(v_fst_517_);
lean_dec(v_a_516_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_536_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___y_523_; uint8_t v___y_528_; size_t v___x_530_; size_t v___x_531_; uint8_t v___x_532_; 
v___x_530_ = lean_ptr_addr(v_fn_509_);
v___x_531_ = lean_ptr_addr(v_fst_513_);
v___x_532_ = lean_usize_dec_eq(v___x_530_, v___x_531_);
if (v___x_532_ == 0)
{
v___y_528_ = v___x_532_;
goto v___jp_527_;
}
else
{
size_t v___x_533_; size_t v___x_534_; uint8_t v___x_535_; 
v___x_533_ = lean_ptr_addr(v_arg_510_);
v___x_534_ = lean_ptr_addr(v_fst_517_);
v___x_535_ = lean_usize_dec_eq(v___x_533_, v___x_534_);
v___y_528_ = v___x_535_;
goto v___jp_527_;
}
v___jp_522_:
{
lean_object* v___x_525_; 
lean_inc_ref(v___y_523_);
if (v_isShared_521_ == 0)
{
lean_ctor_set(v___x_520_, 0, v___y_523_);
v___x_525_ = v___x_520_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v___y_523_);
lean_ctor_set(v_reuseFailAlloc_526_, 1, v_snd_518_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
v_a_417_ = v___x_525_;
v_fst_418_ = v___y_523_;
goto v___jp_416_;
}
}
v___jp_527_:
{
if (v___y_528_ == 0)
{
lean_object* v___x_529_; 
v___x_529_ = l_Lean_Expr_app___override(v_fst_513_, v_fst_517_);
v___y_523_ = v___x_529_;
goto v___jp_522_;
}
else
{
lean_dec(v_fst_517_);
lean_dec(v_fst_513_);
lean_inc_ref(v_e_410_);
v___y_523_ = v_e_410_;
goto v___jp_522_;
}
}
}
}
else
{
lean_dec(v_fst_513_);
v___y_424_ = v___x_515_;
goto v___jp_423_;
}
}
else
{
v___y_424_ = v___x_511_;
goto v___jp_423_;
}
}
case 10:
{
lean_object* v_data_537_; lean_object* v_expr_538_; lean_object* v___x_539_; 
v_data_537_ = lean_ctor_get(v_e_410_, 0);
v_expr_538_ = lean_ctor_get(v_e_410_, 1);
lean_inc_ref(v_expr_538_);
v___x_539_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go(v_expr_538_, v_a_411_, v_a_412_, v_a_413_, v_a_414_);
if (lean_obj_tag(v___x_539_) == 0)
{
lean_object* v_a_540_; lean_object* v_fst_541_; lean_object* v_snd_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_555_; 
v_a_540_ = lean_ctor_get(v___x_539_, 0);
lean_inc(v_a_540_);
lean_dec_ref(v___x_539_);
v_fst_541_ = lean_ctor_get(v_a_540_, 0);
v_snd_542_ = lean_ctor_get(v_a_540_, 1);
v_isSharedCheck_555_ = !lean_is_exclusive(v_a_540_);
if (v_isSharedCheck_555_ == 0)
{
v___x_544_ = v_a_540_;
v_isShared_545_ = v_isSharedCheck_555_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_snd_542_);
lean_inc(v_fst_541_);
lean_dec(v_a_540_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_555_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___y_547_; size_t v___x_551_; size_t v___x_552_; uint8_t v___x_553_; 
v___x_551_ = lean_ptr_addr(v_expr_538_);
v___x_552_ = lean_ptr_addr(v_fst_541_);
v___x_553_ = lean_usize_dec_eq(v___x_551_, v___x_552_);
if (v___x_553_ == 0)
{
lean_object* v___x_554_; 
lean_inc(v_data_537_);
v___x_554_ = l_Lean_Expr_mdata___override(v_data_537_, v_fst_541_);
v___y_547_ = v___x_554_;
goto v___jp_546_;
}
else
{
lean_dec(v_fst_541_);
lean_inc_ref(v_e_410_);
v___y_547_ = v_e_410_;
goto v___jp_546_;
}
v___jp_546_:
{
lean_object* v___x_549_; 
lean_inc_ref(v___y_547_);
if (v_isShared_545_ == 0)
{
lean_ctor_set(v___x_544_, 0, v___y_547_);
v___x_549_ = v___x_544_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v___y_547_);
lean_ctor_set(v_reuseFailAlloc_550_, 1, v_snd_542_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
v_a_417_ = v___x_549_;
v_fst_418_ = v___y_547_;
goto v___jp_416_;
}
}
}
}
else
{
v___y_424_ = v___x_539_;
goto v___jp_423_;
}
}
case 11:
{
lean_object* v_typeName_556_; lean_object* v_idx_557_; lean_object* v_struct_558_; lean_object* v___x_559_; 
v_typeName_556_ = lean_ctor_get(v_e_410_, 0);
v_idx_557_ = lean_ctor_get(v_e_410_, 1);
v_struct_558_ = lean_ctor_get(v_e_410_, 2);
lean_inc_ref(v_struct_558_);
v___x_559_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go(v_struct_558_, v_a_411_, v_a_412_, v_a_413_, v_a_414_);
if (lean_obj_tag(v___x_559_) == 0)
{
lean_object* v_a_560_; lean_object* v_fst_561_; lean_object* v_snd_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_575_; 
v_a_560_ = lean_ctor_get(v___x_559_, 0);
lean_inc(v_a_560_);
lean_dec_ref(v___x_559_);
v_fst_561_ = lean_ctor_get(v_a_560_, 0);
v_snd_562_ = lean_ctor_get(v_a_560_, 1);
v_isSharedCheck_575_ = !lean_is_exclusive(v_a_560_);
if (v_isSharedCheck_575_ == 0)
{
v___x_564_ = v_a_560_;
v_isShared_565_ = v_isSharedCheck_575_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_snd_562_);
lean_inc(v_fst_561_);
lean_dec(v_a_560_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_575_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v___y_567_; size_t v___x_571_; size_t v___x_572_; uint8_t v___x_573_; 
v___x_571_ = lean_ptr_addr(v_struct_558_);
v___x_572_ = lean_ptr_addr(v_fst_561_);
v___x_573_ = lean_usize_dec_eq(v___x_571_, v___x_572_);
if (v___x_573_ == 0)
{
lean_object* v___x_574_; 
lean_inc(v_idx_557_);
lean_inc(v_typeName_556_);
v___x_574_ = l_Lean_Expr_proj___override(v_typeName_556_, v_idx_557_, v_fst_561_);
v___y_567_ = v___x_574_;
goto v___jp_566_;
}
else
{
lean_dec(v_fst_561_);
lean_inc_ref(v_e_410_);
v___y_567_ = v_e_410_;
goto v___jp_566_;
}
v___jp_566_:
{
lean_object* v___x_569_; 
lean_inc_ref(v___y_567_);
if (v_isShared_565_ == 0)
{
lean_ctor_set(v___x_564_, 0, v___y_567_);
v___x_569_ = v___x_564_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v___y_567_);
lean_ctor_set(v_reuseFailAlloc_570_, 1, v_snd_562_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
v_a_417_ = v___x_569_;
v_fst_418_ = v___y_567_;
goto v___jp_416_;
}
}
}
}
else
{
v___y_424_ = v___x_559_;
goto v___jp_423_;
}
}
default: 
{
lean_object* v___x_576_; 
lean_inc_ref_n(v_e_410_, 2);
v___x_576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_576_, 0, v_e_410_);
lean_ctor_set(v___x_576_, 1, v_a_412_);
v_a_417_ = v___x_576_;
v_fst_418_ = v_e_410_;
goto v___jp_416_;
}
}
}
else
{
lean_object* v_e_577_; lean_object* v___x_578_; 
v_e_577_ = l_Lean_Expr_appArg_x21(v_e_410_);
v___x_578_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go(v_e_577_, v_a_411_, v_a_412_, v_a_413_, v_a_414_);
if (lean_obj_tag(v___x_578_) == 0)
{
lean_object* v_a_579_; lean_object* v_fst_580_; lean_object* v_snd_581_; lean_object* v___f_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v_v_585_; 
v_a_579_ = lean_ctor_get(v___x_578_, 0);
lean_inc(v_a_579_);
lean_dec_ref(v___x_578_);
v_fst_580_ = lean_ctor_get(v_a_579_, 0);
lean_inc_n(v_fst_580_, 2);
v_snd_581_ = lean_ctor_get(v_a_579_, 1);
lean_inc(v_snd_581_);
lean_dec(v_a_579_);
v___f_582_ = lean_alloc_closure((void*)(l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___lam__0___boxed), 7, 1);
lean_closure_set(v___f_582_, 0, v_fst_580_);
v___x_583_ = l_Lean_Expr_appFn_x21(v_e_410_);
v___x_584_ = l_Lean_Expr_appFn_x21(v___x_583_);
v_v_585_ = l_Lean_Expr_appArg_x21(v___x_584_);
lean_dec_ref(v___x_584_);
if (lean_obj_tag(v_v_585_) == 0)
{
lean_object* v_deBruijnIndex_586_; lean_object* v_b_587_; lean_object* v___x_588_; 
v_deBruijnIndex_586_ = lean_ctor_get(v_v_585_, 0);
lean_inc(v_deBruijnIndex_586_);
lean_dec_ref(v_v_585_);
v_b_587_ = l_Lean_Expr_appArg_x21(v___x_583_);
lean_dec_ref(v___x_583_);
v___x_588_ = l_Lean_Expr_headBeta(v_b_587_);
switch(lean_obj_tag(v___x_588_))
{
case 6:
{
lean_object* v_binderName_589_; lean_object* v_binderType_590_; lean_object* v_body_591_; uint8_t v_binderInfo_592_; lean_object* v___x_593_; 
lean_dec(v_fst_580_);
v_binderName_589_ = lean_ctor_get(v___x_588_, 0);
lean_inc(v_binderName_589_);
v_binderType_590_ = lean_ctor_get(v___x_588_, 1);
lean_inc_ref(v_binderType_590_);
v_body_591_ = lean_ctor_get(v___x_588_, 2);
lean_inc_ref(v_body_591_);
v_binderInfo_592_ = lean_ctor_get_uint8(v___x_588_, sizeof(void*)*3 + 8);
lean_dec_ref(v___x_588_);
v___x_593_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___lam__1(v___f_582_, v_deBruijnIndex_586_, v_binderName_589_, v_binderType_590_, v_body_591_, v_binderInfo_592_, v_a_411_, v_snd_581_, v_a_413_, v_a_414_);
lean_dec_ref(v_body_591_);
lean_dec_ref(v_binderType_590_);
lean_dec(v_deBruijnIndex_586_);
v___y_424_ = v___x_593_;
goto v___jp_423_;
}
case 7:
{
lean_object* v_binderName_594_; lean_object* v_binderType_595_; lean_object* v_body_596_; uint8_t v_binderInfo_597_; lean_object* v___x_598_; 
lean_dec(v_fst_580_);
v_binderName_594_ = lean_ctor_get(v___x_588_, 0);
lean_inc(v_binderName_594_);
v_binderType_595_ = lean_ctor_get(v___x_588_, 1);
lean_inc_ref(v_binderType_595_);
v_body_596_ = lean_ctor_get(v___x_588_, 2);
lean_inc_ref(v_body_596_);
v_binderInfo_597_ = lean_ctor_get_uint8(v___x_588_, sizeof(void*)*3 + 8);
lean_dec_ref(v___x_588_);
v___x_598_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___lam__1(v___f_582_, v_deBruijnIndex_586_, v_binderName_594_, v_binderType_595_, v_body_596_, v_binderInfo_597_, v_a_411_, v_snd_581_, v_a_413_, v_a_414_);
lean_dec_ref(v_body_596_);
lean_dec_ref(v_binderType_595_);
lean_dec(v_deBruijnIndex_586_);
v___y_424_ = v___x_598_;
goto v___jp_423_;
}
default: 
{
lean_object* v___x_599_; uint8_t v___x_600_; 
lean_dec_ref(v___x_588_);
lean_dec_ref(v___f_582_);
v___x_599_ = lean_array_get_size(v_snd_581_);
v___x_600_ = lean_nat_dec_lt(v_deBruijnIndex_586_, v___x_599_);
if (v___x_600_ == 0)
{
lean_object* v___x_601_; lean_object* v___x_602_; 
lean_dec(v_deBruijnIndex_586_);
lean_dec(v_fst_580_);
v___x_601_ = lean_obj_once(&l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___closed__2, &l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___closed__2_once, _init_l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___closed__2);
v___x_602_ = l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2(v___x_601_, v_a_411_, v_snd_581_, v_a_413_, v_a_414_);
v___y_424_ = v___x_602_;
goto v___jp_423_;
}
else
{
lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_603_ = lean_box(0);
v___x_604_ = lean_nat_sub(v___x_599_, v_deBruijnIndex_586_);
v___x_605_ = lean_unsigned_to_nat(1u);
v___x_606_ = lean_nat_sub(v___x_604_, v___x_605_);
lean_dec(v___x_604_);
v___x_607_ = lean_array_get_borrowed(v___x_603_, v_snd_581_, v___x_606_);
lean_dec(v___x_606_);
lean_inc(v___x_607_);
v___x_608_ = l_Lean_Core_mkFreshUserName(v___x_607_, v_a_413_, v_a_414_);
if (lean_obj_tag(v___x_608_) == 0)
{
lean_object* v_a_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v_a_609_ = lean_ctor_get(v___x_608_, 0);
lean_inc(v_a_609_);
lean_dec_ref(v___x_608_);
v___x_610_ = lean_box(0);
v___x_611_ = l___private_Lean_Meta_BinderNameHint_0__Lean_rememberName(v_deBruijnIndex_586_, v_a_609_, v_snd_581_);
lean_dec(v_deBruijnIndex_586_);
v___x_612_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___lam__0(v_fst_580_, v___x_610_, v_a_411_, v___x_611_, v_a_413_, v_a_414_);
v___y_424_ = v___x_612_;
goto v___jp_423_;
}
else
{
lean_object* v_a_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_620_; 
lean_dec(v_deBruijnIndex_586_);
lean_dec(v_snd_581_);
lean_dec(v_fst_580_);
lean_dec_ref(v_e_410_);
v_a_613_ = lean_ctor_get(v___x_608_, 0);
v_isSharedCheck_620_ = !lean_is_exclusive(v___x_608_);
if (v_isSharedCheck_620_ == 0)
{
v___x_615_ = v___x_608_;
v_isShared_616_ = v_isSharedCheck_620_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_a_613_);
lean_dec(v___x_608_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_620_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v___x_618_; 
if (v_isShared_616_ == 0)
{
v___x_618_ = v___x_615_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v_a_613_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
return v___x_618_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_621_; lean_object* v___x_622_; 
lean_dec_ref(v_v_585_);
lean_dec_ref(v___x_583_);
lean_dec_ref(v___f_582_);
v___x_621_ = lean_box(0);
v___x_622_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___lam__0(v_fst_580_, v___x_621_, v_a_411_, v_snd_581_, v_a_413_, v_a_414_);
v___y_424_ = v___x_622_;
goto v___jp_423_;
}
}
else
{
v___y_424_ = v___x_578_;
goto v___jp_423_;
}
}
}
else
{
lean_object* v_val_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_631_; 
lean_dec_ref(v_e_410_);
v_val_623_ = lean_ctor_get(v___x_428_, 0);
v_isSharedCheck_631_ = !lean_is_exclusive(v___x_428_);
if (v_isSharedCheck_631_ == 0)
{
v___x_625_ = v___x_428_;
v_isShared_626_ = v_isSharedCheck_631_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_val_623_);
lean_dec(v___x_428_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_631_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_627_; lean_object* v___x_629_; 
v___x_627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_627_, 0, v_val_623_);
lean_ctor_set(v___x_627_, 1, v_a_412_);
if (v_isShared_626_ == 0)
{
lean_ctor_set_tag(v___x_625_, 0);
lean_ctor_set(v___x_625_, 0, v___x_627_);
v___x_629_ = v___x_625_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v___x_627_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
}
v___jp_416_:
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_419_ = lean_st_ref_take(v_a_411_);
v___x_420_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0___redArg(v___x_419_, v_e_410_, v_fst_418_);
v___x_421_ = lean_st_ref_set(v_a_411_, v___x_420_);
v___x_422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_422_, 0, v_a_417_);
return v___x_422_;
}
v___jp_423_:
{
if (lean_obj_tag(v___y_424_) == 0)
{
lean_object* v_a_425_; lean_object* v_fst_426_; 
v_a_425_ = lean_ctor_get(v___y_424_, 0);
lean_inc(v_a_425_);
lean_dec_ref(v___y_424_);
v_fst_426_ = lean_ctor_get(v_a_425_, 0);
lean_inc(v_fst_426_);
v_a_417_ = v_a_425_;
v_fst_418_ = v_fst_426_;
goto v___jp_416_;
}
else
{
lean_dec_ref(v_e_410_);
return v___y_424_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___boxed(lean_object* v_e_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go(v_e_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_);
lean_dec(v_a_636_);
lean_dec_ref(v_a_635_);
lean_dec(v_a_633_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0(lean_object* v_00_u03b2_639_, lean_object* v_m_640_, lean_object* v_a_641_, lean_object* v_b_642_){
_start:
{
lean_object* v___x_643_; 
v___x_643_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0___redArg(v_m_640_, v_a_641_, v_b_642_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1(lean_object* v_00_u03b2_644_, lean_object* v_m_645_, lean_object* v_a_646_){
_start:
{
lean_object* v___x_647_; 
v___x_647_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1___redArg(v_m_645_, v_a_646_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1___boxed(lean_object* v_00_u03b2_648_, lean_object* v_m_649_, lean_object* v_a_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1(v_00_u03b2_648_, v_m_649_, v_a_650_);
lean_dec_ref(v_a_650_);
lean_dec_ref(v_m_649_);
return v_res_651_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__0(lean_object* v_00_u03b2_652_, lean_object* v_a_653_, lean_object* v_x_654_){
_start:
{
uint8_t v___x_655_; 
v___x_655_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__0___redArg(v_a_653_, v_x_654_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_656_, lean_object* v_a_657_, lean_object* v_x_658_){
_start:
{
uint8_t v_res_659_; lean_object* v_r_660_; 
v_res_659_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__0(v_00_u03b2_656_, v_a_657_, v_x_658_);
lean_dec(v_x_658_);
lean_dec_ref(v_a_657_);
v_r_660_ = lean_box(v_res_659_);
return v_r_660_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__1(lean_object* v_00_u03b2_661_, lean_object* v_data_662_){
_start:
{
lean_object* v___x_663_; 
v___x_663_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__1___redArg(v_data_662_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__2(lean_object* v_00_u03b2_664_, lean_object* v_a_665_, lean_object* v_b_666_, lean_object* v_x_667_){
_start:
{
lean_object* v___x_668_; 
v___x_668_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__2___redArg(v_a_665_, v_b_666_, v_x_667_);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1_spec__4(lean_object* v_00_u03b2_669_, lean_object* v_a_670_, lean_object* v_x_671_){
_start:
{
lean_object* v___x_672_; 
v___x_672_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1_spec__4___redArg(v_a_670_, v_x_671_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1_spec__4___boxed(lean_object* v_00_u03b2_673_, lean_object* v_a_674_, lean_object* v_x_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1_spec__4(v_00_u03b2_673_, v_a_674_, v_x_675_);
lean_dec(v_x_675_);
lean_dec_ref(v_a_674_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_677_, lean_object* v_i_678_, lean_object* v_source_679_, lean_object* v_target_680_){
_start:
{
lean_object* v___x_681_; 
v___x_681_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__1_spec__3___redArg(v_i_678_, v_source_679_, v_target_680_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_682_, lean_object* v_x_683_, lean_object* v_x_684_){
_start:
{
lean_object* v___x_685_; 
v___x_685_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__1_spec__3_spec__5___redArg(v_x_683_, v_x_684_);
return v___x_685_;
}
}
static lean_object* _init_l_Lean_Expr_resolveBinderNameHint___closed__0(void){
_start:
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_686_ = lean_box(0);
v___x_687_ = lean_unsigned_to_nat(16u);
v___x_688_ = lean_mk_array(v___x_687_, v___x_686_);
return v___x_688_;
}
}
static lean_object* _init_l_Lean_Expr_resolveBinderNameHint___closed__1(void){
_start:
{
lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_689_ = lean_obj_once(&l_Lean_Expr_resolveBinderNameHint___closed__0, &l_Lean_Expr_resolveBinderNameHint___closed__0_once, _init_l_Lean_Expr_resolveBinderNameHint___closed__0);
v___x_690_ = lean_unsigned_to_nat(0u);
v___x_691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_691_, 0, v___x_690_);
lean_ctor_set(v___x_691_, 1, v___x_689_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_resolveBinderNameHint(lean_object* v_e_694_, lean_object* v_a_695_, lean_object* v_a_696_){
_start:
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_698_ = lean_obj_once(&l_Lean_Expr_resolveBinderNameHint___closed__1, &l_Lean_Expr_resolveBinderNameHint___closed__1_once, _init_l_Lean_Expr_resolveBinderNameHint___closed__1);
v___x_699_ = lean_st_mk_ref(v___x_698_);
v___x_700_ = ((lean_object*)(l_Lean_Expr_resolveBinderNameHint___closed__2));
v___x_701_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go(v_e_694_, v___x_699_, v___x_700_, v_a_695_, v_a_696_);
if (lean_obj_tag(v___x_701_) == 0)
{
lean_object* v_a_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_711_; 
v_a_702_ = lean_ctor_get(v___x_701_, 0);
v_isSharedCheck_711_ = !lean_is_exclusive(v___x_701_);
if (v_isSharedCheck_711_ == 0)
{
v___x_704_ = v___x_701_;
v_isShared_705_ = v_isSharedCheck_711_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_a_702_);
lean_dec(v___x_701_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_711_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v_fst_706_; lean_object* v___x_707_; lean_object* v___x_709_; 
v_fst_706_ = lean_ctor_get(v_a_702_, 0);
lean_inc(v_fst_706_);
lean_dec(v_a_702_);
v___x_707_ = lean_st_ref_get(v___x_699_);
lean_dec(v___x_699_);
lean_dec(v___x_707_);
if (v_isShared_705_ == 0)
{
lean_ctor_set(v___x_704_, 0, v_fst_706_);
v___x_709_ = v___x_704_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_fst_706_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
}
else
{
lean_object* v_a_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_719_; 
lean_dec(v___x_699_);
v_a_712_ = lean_ctor_get(v___x_701_, 0);
v_isSharedCheck_719_ = !lean_is_exclusive(v___x_701_);
if (v_isSharedCheck_719_ == 0)
{
v___x_714_ = v___x_701_;
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_a_712_);
lean_dec(v___x_701_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_717_; 
if (v_isShared_715_ == 0)
{
v___x_717_ = v___x_714_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_a_712_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_resolveBinderNameHint___boxed(lean_object* v_e_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l_Lean_Expr_resolveBinderNameHint(v_e_720_, v_a_721_, v_a_722_);
lean_dec(v_a_722_);
lean_dec_ref(v_a_721_);
return v_res_724_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_BinderNameHint(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
