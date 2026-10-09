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
lean_object* l_Array_instInhabited___redArg();
lean_object* l_instMonadEIO___redArg();
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
lean_object* l_Lean_Core_instInhabitedCoreM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_makeFresh_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instInhabitedCoreM___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
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
uint8_t l_Lean_Expr_hasBinderNameHint___lam__0(lean_object* v_e_4_){
_start:
{
lean_object* v___x_5_; uint8_t v___x_6_; 
v___x_5_ = ((lean_object*)(l_Lean_Expr_hasBinderNameHint___lam__0___closed__1));
v___x_6_ = l_Lean_Expr_isConstOf(v_e_4_, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT void l_Lean_Expr_hasBinderNameHint___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4_ = stack[0].m_obj;
uint8_t v_res_7_;
v_res_7_ = l_Lean_Expr_hasBinderNameHint___lam__0(v_e_4_);
stack->m_num = v_res_7_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasBinderNameHint___lam__0___boxed(lean_object* v_e_8_){
_start:
{
uint8_t v_res_9_; lean_object* v_r_10_; 
v_res_9_ = l_Lean_Expr_hasBinderNameHint___lam__0(v_e_8_);
lean_dec_ref(v_e_8_);
v_r_10_ = lean_box(v_res_9_);
return v_r_10_;
}
}
uint8_t l_Lean_Expr_hasBinderNameHint(lean_object* v_e_12_){
_start:
{
lean_object* v___f_13_; lean_object* v___x_14_; 
v___f_13_ = ((lean_object*)(l_Lean_Expr_hasBinderNameHint___closed__0));
v___x_14_ = lean_find_expr(v___f_13_, v_e_12_);
if (lean_obj_tag(v___x_14_) == 0)
{
uint8_t v___x_15_; 
v___x_15_ = 0;
return v___x_15_;
}
else
{
uint8_t v___x_16_; 
lean_dec_ref_known(v___x_14_, 1);
v___x_16_ = 1;
return v___x_16_;
}
}
}
LEAN_EXPORT void l_Lean_Expr_hasBinderNameHint_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_12_ = stack[0].m_obj;
uint8_t v_res_17_;
v_res_17_ = l_Lean_Expr_hasBinderNameHint(v_e_12_);
stack->m_num = v_res_17_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasBinderNameHint___boxed(lean_object* v_e_18_){
_start:
{
uint8_t v_res_19_; lean_object* v_r_20_; 
v_res_19_ = l_Lean_Expr_hasBinderNameHint(v_e_18_);
lean_dec_ref(v_e_18_);
v_r_20_ = lean_box(v_res_19_);
return v_r_20_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_BinderNameHint_0__Lean_enterScope(lean_object* v_name_21_, lean_object* v_xs_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = lean_array_push(v_xs_22_, v_name_21_);
return v___x_23_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_exitScope_spec__0___closed__0(void){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = l_Array_instInhabited___redArg();
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_exitScope_spec__0(lean_object* v_msg_25_){
_start:
{
lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_26_ = lean_box(0);
v___x_27_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_exitScope_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_exitScope_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_exitScope_spec__0___closed__0);
v___x_28_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_28_, 0, v___x_26_);
lean_ctor_set(v___x_28_, 1, v___x_27_);
v___x_29_ = lean_panic_fn_borrowed(v___x_28_, v_msg_25_);
lean_dec_ref_known(v___x_28_, 2);
return v___x_29_;
}
}
static lean_object* _init_l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope___closed__3(void){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_33_ = ((lean_object*)(l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope___closed__2));
v___x_34_ = lean_unsigned_to_nat(4u);
v___x_35_ = lean_unsigned_to_nat(26u);
v___x_36_ = ((lean_object*)(l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope___closed__1));
v___x_37_ = ((lean_object*)(l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope___closed__0));
v___x_38_ = l_mkPanicMessageWithDecl(v___x_37_, v___x_36_, v___x_35_, v___x_34_, v___x_33_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope(lean_object* v_xs_39_){
_start:
{
lean_object* v___x_40_; lean_object* v___x_41_; uint8_t v___x_42_; 
v___x_40_ = lean_unsigned_to_nat(0u);
v___x_41_ = lean_array_get_size(v_xs_39_);
v___x_42_ = lean_nat_dec_lt(v___x_40_, v___x_41_);
if (v___x_42_ == 0)
{
lean_object* v___x_43_; lean_object* v___x_44_; 
lean_dec_ref(v_xs_39_);
v___x_43_ = lean_obj_once(&l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope___closed__3, &l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope___closed__3_once, _init_l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope___closed__3);
v___x_44_ = l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_exitScope_spec__0(v___x_43_);
return v___x_44_;
}
else
{
lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_45_ = lean_box(0);
v___x_46_ = lean_unsigned_to_nat(1u);
v___x_47_ = lean_nat_sub(v___x_41_, v___x_46_);
v___x_48_ = lean_array_get(v___x_45_, v_xs_39_, v___x_47_);
lean_dec(v___x_47_);
v___x_49_ = lean_array_pop(v_xs_39_);
v___x_50_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_50_, 0, v___x_48_);
lean_ctor_set(v___x_50_, 1, v___x_49_);
return v___x_50_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_rememberName_spec__0(lean_object* v_msg_51_){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_52_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_exitScope_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_exitScope_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_exitScope_spec__0___closed__0);
v___x_53_ = lean_panic_fn_borrowed(v___x_52_, v_msg_51_);
return v___x_53_;
}
}
static lean_object* _init_l___private_Lean_Meta_BinderNameHint_0__Lean_rememberName___closed__2(void){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_56_ = ((lean_object*)(l___private_Lean_Meta_BinderNameHint_0__Lean_rememberName___closed__1));
v___x_57_ = lean_unsigned_to_nat(4u);
v___x_58_ = lean_unsigned_to_nat(30u);
v___x_59_ = ((lean_object*)(l___private_Lean_Meta_BinderNameHint_0__Lean_rememberName___closed__0));
v___x_60_ = ((lean_object*)(l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope___closed__0));
v___x_61_ = l_mkPanicMessageWithDecl(v___x_60_, v___x_59_, v___x_58_, v___x_57_, v___x_56_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_BinderNameHint_0__Lean_rememberName(lean_object* v_bidx_62_, lean_object* v_name_63_, lean_object* v_xs_64_){
_start:
{
lean_object* v___x_65_; uint8_t v___x_66_; 
v___x_65_ = lean_array_get_size(v_xs_64_);
v___x_66_ = lean_nat_dec_lt(v_bidx_62_, v___x_65_);
if (v___x_66_ == 0)
{
lean_object* v___x_67_; lean_object* v___x_68_; 
lean_dec_ref(v_xs_64_);
lean_dec(v_name_63_);
v___x_67_ = lean_obj_once(&l___private_Lean_Meta_BinderNameHint_0__Lean_rememberName___closed__2, &l___private_Lean_Meta_BinderNameHint_0__Lean_rememberName___closed__2_once, _init_l___private_Lean_Meta_BinderNameHint_0__Lean_rememberName___closed__2);
v___x_68_ = l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_rememberName_spec__0(v___x_67_);
return v___x_68_;
}
else
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_69_ = lean_nat_sub(v___x_65_, v_bidx_62_);
v___x_70_ = lean_unsigned_to_nat(1u);
v___x_71_ = lean_nat_sub(v___x_69_, v___x_70_);
lean_dec(v___x_69_);
v___x_72_ = lean_array_set(v_xs_64_, v___x_71_, v_name_63_);
lean_dec(v___x_71_);
return v___x_72_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_BinderNameHint_0__Lean_rememberName___boxed(lean_object* v_bidx_73_, lean_object* v_name_74_, lean_object* v_xs_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l___private_Lean_Meta_BinderNameHint_0__Lean_rememberName(v_bidx_73_, v_name_74_, v_xs_75_);
lean_dec(v_bidx_73_);
return v_res_76_;
}
}
lean_object* l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_makeFresh_spec__0(lean_object* v_msg_78_, lean_object* v___y_79_, lean_object* v___y_80_){
_start:
{
lean_object* v___f_82_; lean_object* v___x_273__overap_83_; lean_object* v___x_84_; 
v___f_82_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_makeFresh_spec__0___closed__0));
v___x_273__overap_83_ = lean_panic_fn_borrowed(v___f_82_, v_msg_78_);
lean_inc(v___y_80_);
lean_inc_ref(v___y_79_);
v___x_84_ = lean_apply_3(v___x_273__overap_83_, v___y_79_, v___y_80_, lean_box(0));
return v___x_84_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_makeFresh_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_78_ = stack[0].m_obj;
lean_object* v___y_79_ = stack[1].m_obj;
lean_object* v___y_80_ = stack[2].m_obj;
lean_object* v_res_85_;
v_res_85_ = l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_makeFresh_spec__0(v_msg_78_, v___y_79_, v___y_80_);
stack->m_obj
 = v_res_85_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_makeFresh_spec__0___boxed(lean_object* v_msg_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_makeFresh_spec__0(v_msg_86_, v___y_87_, v___y_88_);
lean_dec(v___y_88_);
lean_dec_ref(v___y_87_);
return v_res_90_;
}
}
static lean_object* _init_l___private_Lean_Meta_BinderNameHint_0__Lean_makeFresh___closed__1(void){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_92_ = ((lean_object*)(l___private_Lean_Meta_BinderNameHint_0__Lean_rememberName___closed__1));
v___x_93_ = lean_unsigned_to_nat(4u);
v___x_94_ = lean_unsigned_to_nat(34u);
v___x_95_ = ((lean_object*)(l___private_Lean_Meta_BinderNameHint_0__Lean_makeFresh___closed__0));
v___x_96_ = ((lean_object*)(l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope___closed__0));
v___x_97_ = l_mkPanicMessageWithDecl(v___x_96_, v___x_95_, v___x_94_, v___x_93_, v___x_92_);
return v___x_97_;
}
}
lean_object* l___private_Lean_Meta_BinderNameHint_0__Lean_makeFresh(lean_object* v_bidx_98_, lean_object* v_xs_99_, lean_object* v_a_100_, lean_object* v_a_101_){
_start:
{
lean_object* v___x_103_; uint8_t v___x_104_; 
v___x_103_ = lean_array_get_size(v_xs_99_);
v___x_104_ = lean_nat_dec_lt(v_bidx_98_, v___x_103_);
if (v___x_104_ == 0)
{
lean_object* v___x_105_; lean_object* v___x_106_; 
lean_dec_ref(v_xs_99_);
v___x_105_ = lean_obj_once(&l___private_Lean_Meta_BinderNameHint_0__Lean_makeFresh___closed__1, &l___private_Lean_Meta_BinderNameHint_0__Lean_makeFresh___closed__1_once, _init_l___private_Lean_Meta_BinderNameHint_0__Lean_makeFresh___closed__1);
v___x_106_ = l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_makeFresh_spec__0(v___x_105_, v_a_100_, v_a_101_);
return v___x_106_;
}
else
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v_name_111_; lean_object* v___x_112_; 
v___x_107_ = lean_box(0);
v___x_108_ = lean_nat_sub(v___x_103_, v_bidx_98_);
v___x_109_ = lean_unsigned_to_nat(1u);
v___x_110_ = lean_nat_sub(v___x_108_, v___x_109_);
lean_dec(v___x_108_);
v_name_111_ = lean_array_get_borrowed(v___x_107_, v_xs_99_, v___x_110_);
lean_inc(v_name_111_);
v___x_112_ = l_Lean_Core_mkFreshUserName(v_name_111_, v_a_100_, v_a_101_);
if (lean_obj_tag(v___x_112_) == 0)
{
lean_object* v_a_113_; lean_object* v___x_115_; uint8_t v_isShared_116_; uint8_t v_isSharedCheck_121_; 
v_a_113_ = lean_ctor_get(v___x_112_, 0);
v_isSharedCheck_121_ = !lean_is_exclusive(v___x_112_);
if (v_isSharedCheck_121_ == 0)
{
v___x_115_ = v___x_112_;
v_isShared_116_ = v_isSharedCheck_121_;
goto v_resetjp_114_;
}
else
{
lean_inc(v_a_113_);
lean_dec(v___x_112_);
v___x_115_ = lean_box(0);
v_isShared_116_ = v_isSharedCheck_121_;
goto v_resetjp_114_;
}
v_resetjp_114_:
{
lean_object* v___x_117_; lean_object* v___x_119_; 
v___x_117_ = lean_array_set(v_xs_99_, v___x_110_, v_a_113_);
lean_dec(v___x_110_);
if (v_isShared_116_ == 0)
{
lean_ctor_set(v___x_115_, 0, v___x_117_);
v___x_119_ = v___x_115_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_120_; 
v_reuseFailAlloc_120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_120_, 0, v___x_117_);
v___x_119_ = v_reuseFailAlloc_120_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
return v___x_119_;
}
}
}
else
{
lean_object* v_a_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_129_; 
lean_dec(v___x_110_);
lean_dec_ref(v_xs_99_);
v_a_122_ = lean_ctor_get(v___x_112_, 0);
v_isSharedCheck_129_ = !lean_is_exclusive(v___x_112_);
if (v_isSharedCheck_129_ == 0)
{
v___x_124_ = v___x_112_;
v_isShared_125_ = v_isSharedCheck_129_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_a_122_);
lean_dec(v___x_112_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_129_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v___x_127_; 
if (v_isShared_125_ == 0)
{
v___x_127_ = v___x_124_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v_a_122_);
v___x_127_ = v_reuseFailAlloc_128_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
return v___x_127_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_BinderNameHint_0__Lean_makeFresh_0interp(lean_interpreter_value* stack)
{
lean_object* v_bidx_98_ = stack[0].m_obj;
lean_object* v_xs_99_ = stack[1].m_obj;
lean_object* v_a_100_ = stack[2].m_obj;
lean_object* v_a_101_ = stack[3].m_obj;
lean_object* v_res_130_;
v_res_130_ = l___private_Lean_Meta_BinderNameHint_0__Lean_makeFresh(v_bidx_98_, v_xs_99_, v_a_100_, v_a_101_);
stack->m_obj
 = v_res_130_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_BinderNameHint_0__Lean_makeFresh___boxed(lean_object* v_bidx_131_, lean_object* v_xs_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l___private_Lean_Meta_BinderNameHint_0__Lean_makeFresh(v_bidx_131_, v_xs_132_, v_a_133_, v_a_134_);
lean_dec(v_a_134_);
lean_dec_ref(v_a_133_);
lean_dec(v_bidx_131_);
return v_res_136_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2___closed__0(void){
_start:
{
lean_object* v___x_137_; 
v___x_137_ = l_instMonadEIO___redArg();
return v___x_137_;
}
}
lean_object* l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2(lean_object* v_msg_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v_toApplicative_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_195_; 
v___x_148_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2___closed__0, &l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2___closed__0);
v___x_149_ = l_StateRefT_x27_instMonad___redArg(v___x_148_);
v_toApplicative_150_ = lean_ctor_get(v___x_149_, 0);
v_isSharedCheck_195_ = !lean_is_exclusive(v___x_149_);
if (v_isSharedCheck_195_ == 0)
{
lean_object* v_unused_196_; 
v_unused_196_ = lean_ctor_get(v___x_149_, 1);
lean_dec(v_unused_196_);
v___x_152_ = v___x_149_;
v_isShared_153_ = v_isSharedCheck_195_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_toApplicative_150_);
lean_dec(v___x_149_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_195_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v_toFunctor_154_; lean_object* v_toSeq_155_; lean_object* v_toSeqLeft_156_; lean_object* v_toSeqRight_157_; lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_193_; 
v_toFunctor_154_ = lean_ctor_get(v_toApplicative_150_, 0);
v_toSeq_155_ = lean_ctor_get(v_toApplicative_150_, 2);
v_toSeqLeft_156_ = lean_ctor_get(v_toApplicative_150_, 3);
v_toSeqRight_157_ = lean_ctor_get(v_toApplicative_150_, 4);
v_isSharedCheck_193_ = !lean_is_exclusive(v_toApplicative_150_);
if (v_isSharedCheck_193_ == 0)
{
lean_object* v_unused_194_; 
v_unused_194_ = lean_ctor_get(v_toApplicative_150_, 1);
lean_dec(v_unused_194_);
v___x_159_ = v_toApplicative_150_;
v_isShared_160_ = v_isSharedCheck_193_;
goto v_resetjp_158_;
}
else
{
lean_inc(v_toSeqRight_157_);
lean_inc(v_toSeqLeft_156_);
lean_inc(v_toSeq_155_);
lean_inc(v_toFunctor_154_);
lean_dec(v_toApplicative_150_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_193_;
goto v_resetjp_158_;
}
v_resetjp_158_:
{
lean_object* v___f_161_; lean_object* v___f_162_; lean_object* v___f_163_; lean_object* v___f_164_; lean_object* v___x_165_; lean_object* v___f_166_; lean_object* v___f_167_; lean_object* v___f_168_; lean_object* v___x_170_; 
v___f_161_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2___closed__1));
v___f_162_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2___closed__2));
lean_inc_ref(v_toFunctor_154_);
v___f_163_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_163_, 0, v_toFunctor_154_);
v___f_164_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_164_, 0, v_toFunctor_154_);
v___x_165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_165_, 0, v___f_163_);
lean_ctor_set(v___x_165_, 1, v___f_164_);
v___f_166_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_166_, 0, v_toSeqRight_157_);
v___f_167_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_167_, 0, v_toSeqLeft_156_);
v___f_168_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_168_, 0, v_toSeq_155_);
if (v_isShared_160_ == 0)
{
lean_ctor_set(v___x_159_, 4, v___f_166_);
lean_ctor_set(v___x_159_, 3, v___f_167_);
lean_ctor_set(v___x_159_, 2, v___f_168_);
lean_ctor_set(v___x_159_, 1, v___f_161_);
lean_ctor_set(v___x_159_, 0, v___x_165_);
v___x_170_ = v___x_159_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v___x_165_);
lean_ctor_set(v_reuseFailAlloc_192_, 1, v___f_161_);
lean_ctor_set(v_reuseFailAlloc_192_, 2, v___f_168_);
lean_ctor_set(v_reuseFailAlloc_192_, 3, v___f_167_);
lean_ctor_set(v_reuseFailAlloc_192_, 4, v___f_166_);
v___x_170_ = v_reuseFailAlloc_192_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
lean_object* v___x_172_; 
if (v_isShared_153_ == 0)
{
lean_ctor_set(v___x_152_, 1, v___f_162_);
lean_ctor_set(v___x_152_, 0, v___x_170_);
v___x_172_ = v___x_152_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v___x_170_);
lean_ctor_set(v_reuseFailAlloc_191_, 1, v___f_162_);
v___x_172_ = v_reuseFailAlloc_191_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___f_176_; lean_object* v___f_177_; lean_object* v___f_178_; lean_object* v___f_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_13027__overap_189_; lean_object* v___x_190_; 
v___x_173_ = lean_box(0);
v___x_174_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2___closed__3));
v___x_175_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2___closed__4));
lean_inc_ref_n(v___x_172_, 6);
v___f_176_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_176_, 0, v___x_172_);
v___f_177_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_177_, 0, v___x_172_);
v___f_178_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_178_, 0, v___x_172_);
v___f_179_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_179_, 0, v___x_172_);
v___x_180_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_180_, 0, lean_box(0));
lean_closure_set(v___x_180_, 1, lean_box(0));
lean_closure_set(v___x_180_, 2, v___x_172_);
v___x_181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_181_, 0, v___x_180_);
lean_ctor_set(v___x_181_, 1, v___f_176_);
v___x_182_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_182_, 0, lean_box(0));
lean_closure_set(v___x_182_, 1, lean_box(0));
lean_closure_set(v___x_182_, 2, v___x_172_);
v___x_183_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_183_, 0, v___x_181_);
lean_ctor_set(v___x_183_, 1, v___x_182_);
lean_ctor_set(v___x_183_, 2, v___f_177_);
lean_ctor_set(v___x_183_, 3, v___f_178_);
lean_ctor_set(v___x_183_, 4, v___f_179_);
v___x_184_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_184_, 0, lean_box(0));
lean_closure_set(v___x_184_, 1, lean_box(0));
lean_closure_set(v___x_184_, 2, v___x_172_);
v___x_185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_185_, 0, v___x_183_);
lean_ctor_set(v___x_185_, 1, v___x_184_);
v___x_186_ = l_Lean_MonadCacheT_instMonad___redArg(v___x_173_, v___x_174_, v___x_175_, v___x_185_);
v___x_187_ = l_Lean_instInhabitedExpr;
v___x_188_ = l_instInhabitedOfMonad___redArg(v___x_186_, v___x_187_);
v___x_13027__overap_189_ = lean_panic_fn_borrowed(v___x_188_, v_msg_142_);
lean_dec(v___x_188_);
lean_inc(v___y_146_);
lean_inc_ref(v___y_145_);
lean_inc(v___y_143_);
v___x_190_ = lean_apply_5(v___x_13027__overap_189_, v___y_143_, v___y_144_, v___y_145_, v___y_146_, lean_box(0));
return v___x_190_;
}
}
}
}
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_142_ = stack[0].m_obj;
lean_object* v___y_143_ = stack[1].m_obj;
lean_object* v___y_144_ = stack[2].m_obj;
lean_object* v___y_145_ = stack[3].m_obj;
lean_object* v___y_146_ = stack[4].m_obj;
lean_object* v_res_197_;
v_res_197_ = l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2(v_msg_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_);
stack->m_obj
 = v_res_197_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2___boxed(lean_object* v_msg_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2(v_msg_198_, v___y_199_, v___y_200_, v___y_201_, v___y_202_);
lean_dec(v___y_202_);
lean_dec_ref(v___y_201_);
lean_dec(v___y_199_);
return v_res_204_;
}
}
lean_object* l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___lam__0(lean_object* v_fst_205_, lean_object* v_____r_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_212_, 0, v_fst_205_);
lean_ctor_set(v___x_212_, 1, v___y_208_);
v___x_213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_213_, 0, v___x_212_);
return v___x_213_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fst_205_ = stack[0].m_obj;
lean_object* v_____r_206_ = stack[1].m_obj;
lean_object* v___y_207_ = stack[2].m_obj;
lean_object* v___y_208_ = stack[3].m_obj;
lean_object* v___y_209_ = stack[4].m_obj;
lean_object* v___y_210_ = stack[5].m_obj;
lean_object* v_res_214_;
v_res_214_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___lam__0(v_fst_205_, v_____r_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_);
stack->m_obj
 = v_res_214_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___lam__0___boxed(lean_object* v_fst_215_, lean_object* v_____r_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___lam__0(v_fst_215_, v_____r_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_);
lean_dec(v___y_220_);
lean_dec_ref(v___y_219_);
lean_dec(v___y_217_);
return v_res_222_;
}
}
lean_object* l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___lam__1(lean_object* v___f_223_, lean_object* v_bidx_224_, lean_object* v_n_225_, lean_object* v_binderType_226_, lean_object* v_body_227_, uint8_t v_binderInfo_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_){
_start:
{
lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_234_ = lean_box(0);
v___x_235_ = l___private_Lean_Meta_BinderNameHint_0__Lean_rememberName(v_bidx_224_, v_n_225_, v___y_230_);
lean_inc(v___y_232_);
lean_inc_ref(v___y_231_);
lean_inc(v___y_229_);
v___x_236_ = lean_apply_6(v___f_223_, v___x_234_, v___y_229_, v___x_235_, v___y_231_, v___y_232_, lean_box(0));
return v___x_236_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_223_ = stack[0].m_obj;
lean_object* v_bidx_224_ = stack[1].m_obj;
lean_object* v_n_225_ = stack[2].m_obj;
lean_object* v_binderType_226_ = stack[3].m_obj;
lean_object* v_body_227_ = stack[4].m_obj;
uint8_t v_binderInfo_228_ = stack[5].m_num;
lean_object* v___y_229_ = stack[6].m_obj;
lean_object* v___y_230_ = stack[7].m_obj;
lean_object* v___y_231_ = stack[8].m_obj;
lean_object* v___y_232_ = stack[9].m_obj;
lean_object* v_res_237_;
v_res_237_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___lam__1(v___f_223_, v_bidx_224_, v_n_225_, v_binderType_226_, v_body_227_, v_binderInfo_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_);
stack->m_obj
 = v_res_237_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___lam__1___boxed(lean_object* v___f_238_, lean_object* v_bidx_239_, lean_object* v_n_240_, lean_object* v_binderType_241_, lean_object* v_body_242_, lean_object* v_binderInfo_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_){
_start:
{
uint8_t v_binderInfo_13642__boxed_249_; lean_object* v_res_250_; 
v_binderInfo_13642__boxed_249_ = lean_unbox(v_binderInfo_243_);
v_res_250_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___lam__1(v___f_238_, v_bidx_239_, v_n_240_, v_binderType_241_, v_body_242_, v_binderInfo_13642__boxed_249_, v___y_244_, v___y_245_, v___y_246_, v___y_247_);
lean_dec(v___y_247_);
lean_dec_ref(v___y_246_);
lean_dec(v___y_244_);
lean_dec_ref(v_body_242_);
lean_dec_ref(v_binderType_241_);
lean_dec(v_bidx_239_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__1_spec__3_spec__5___redArg(lean_object* v_x_251_, lean_object* v_x_252_){
_start:
{
if (lean_obj_tag(v_x_252_) == 0)
{
return v_x_251_;
}
else
{
lean_object* v_key_253_; lean_object* v_value_254_; lean_object* v_tail_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_278_; 
v_key_253_ = lean_ctor_get(v_x_252_, 0);
v_value_254_ = lean_ctor_get(v_x_252_, 1);
v_tail_255_ = lean_ctor_get(v_x_252_, 2);
v_isSharedCheck_278_ = !lean_is_exclusive(v_x_252_);
if (v_isSharedCheck_278_ == 0)
{
v___x_257_ = v_x_252_;
v_isShared_258_ = v_isSharedCheck_278_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_tail_255_);
lean_inc(v_value_254_);
lean_inc(v_key_253_);
lean_dec(v_x_252_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_278_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_259_; uint64_t v___x_260_; uint64_t v___x_261_; uint64_t v___x_262_; uint64_t v_fold_263_; uint64_t v___x_264_; uint64_t v___x_265_; uint64_t v___x_266_; size_t v___x_267_; size_t v___x_268_; size_t v___x_269_; size_t v___x_270_; size_t v___x_271_; lean_object* v___x_272_; lean_object* v___x_274_; 
v___x_259_ = lean_array_get_size(v_x_251_);
v___x_260_ = l_Lean_ExprStructEq_hash(v_key_253_);
v___x_261_ = 32ULL;
v___x_262_ = lean_uint64_shift_right(v___x_260_, v___x_261_);
v_fold_263_ = lean_uint64_xor(v___x_260_, v___x_262_);
v___x_264_ = 16ULL;
v___x_265_ = lean_uint64_shift_right(v_fold_263_, v___x_264_);
v___x_266_ = lean_uint64_xor(v_fold_263_, v___x_265_);
v___x_267_ = lean_uint64_to_usize(v___x_266_);
v___x_268_ = lean_usize_of_nat(v___x_259_);
v___x_269_ = ((size_t)1ULL);
v___x_270_ = lean_usize_sub(v___x_268_, v___x_269_);
v___x_271_ = lean_usize_land(v___x_267_, v___x_270_);
v___x_272_ = lean_array_uget_borrowed(v_x_251_, v___x_271_);
lean_inc(v___x_272_);
if (v_isShared_258_ == 0)
{
lean_ctor_set(v___x_257_, 2, v___x_272_);
v___x_274_ = v___x_257_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v_key_253_);
lean_ctor_set(v_reuseFailAlloc_277_, 1, v_value_254_);
lean_ctor_set(v_reuseFailAlloc_277_, 2, v___x_272_);
v___x_274_ = v_reuseFailAlloc_277_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
lean_object* v___x_275_; 
v___x_275_ = lean_array_uset(v_x_251_, v___x_271_, v___x_274_);
v_x_251_ = v___x_275_;
v_x_252_ = v_tail_255_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__1_spec__3___redArg(lean_object* v_i_279_, lean_object* v_source_280_, lean_object* v_target_281_){
_start:
{
lean_object* v___x_282_; uint8_t v___x_283_; 
v___x_282_ = lean_array_get_size(v_source_280_);
v___x_283_ = lean_nat_dec_lt(v_i_279_, v___x_282_);
if (v___x_283_ == 0)
{
lean_dec_ref(v_source_280_);
lean_dec(v_i_279_);
return v_target_281_;
}
else
{
lean_object* v_es_284_; lean_object* v___x_285_; lean_object* v_source_286_; lean_object* v_target_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v_es_284_ = lean_array_fget(v_source_280_, v_i_279_);
v___x_285_ = lean_box(0);
v_source_286_ = lean_array_fset(v_source_280_, v_i_279_, v___x_285_);
v_target_287_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__1_spec__3_spec__5___redArg(v_target_281_, v_es_284_);
v___x_288_ = lean_unsigned_to_nat(1u);
v___x_289_ = lean_nat_add(v_i_279_, v___x_288_);
lean_dec(v_i_279_);
v_i_279_ = v___x_289_;
v_source_280_ = v_source_286_;
v_target_281_ = v_target_287_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__1___redArg(lean_object* v_data_291_){
_start:
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v_nbuckets_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_292_ = lean_array_get_size(v_data_291_);
v___x_293_ = lean_unsigned_to_nat(2u);
v_nbuckets_294_ = lean_nat_mul(v___x_292_, v___x_293_);
v___x_295_ = lean_unsigned_to_nat(0u);
v___x_296_ = lean_box(0);
v___x_297_ = lean_mk_array(v_nbuckets_294_, v___x_296_);
v___x_298_ = lean_array_propagate_mark(v_data_291_, v___x_297_);
v___x_299_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__1_spec__3___redArg(v___x_295_, v_data_291_, v___x_298_);
return v___x_299_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__0___redArg(lean_object* v_a_300_, lean_object* v_x_301_){
_start:
{
if (lean_obj_tag(v_x_301_) == 0)
{
uint8_t v___x_302_; 
v___x_302_ = 0;
return v___x_302_;
}
else
{
lean_object* v_key_303_; lean_object* v_tail_304_; uint8_t v___x_305_; 
v_key_303_ = lean_ctor_get(v_x_301_, 0);
v_tail_304_ = lean_ctor_get(v_x_301_, 2);
v___x_305_ = l_Lean_ExprStructEq_beq(v_key_303_, v_a_300_);
if (v___x_305_ == 0)
{
v_x_301_ = v_tail_304_;
goto _start;
}
else
{
return v___x_305_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_300_ = stack[0].m_obj;
lean_object* v_x_301_ = stack[1].m_obj;
uint8_t v_res_307_;
v_res_307_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__0___redArg(v_a_300_, v_x_301_);
stack->m_num = v_res_307_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__0___redArg___boxed(lean_object* v_a_308_, lean_object* v_x_309_){
_start:
{
uint8_t v_res_310_; lean_object* v_r_311_; 
v_res_310_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__0___redArg(v_a_308_, v_x_309_);
lean_dec(v_x_309_);
lean_dec_ref(v_a_308_);
v_r_311_ = lean_box(v_res_310_);
return v_r_311_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__2___redArg(lean_object* v_a_312_, lean_object* v_b_313_, lean_object* v_x_314_){
_start:
{
if (lean_obj_tag(v_x_314_) == 0)
{
lean_dec(v_b_313_);
lean_dec_ref(v_a_312_);
return v_x_314_;
}
else
{
lean_object* v_key_315_; lean_object* v_value_316_; lean_object* v_tail_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_329_; 
v_key_315_ = lean_ctor_get(v_x_314_, 0);
v_value_316_ = lean_ctor_get(v_x_314_, 1);
v_tail_317_ = lean_ctor_get(v_x_314_, 2);
v_isSharedCheck_329_ = !lean_is_exclusive(v_x_314_);
if (v_isSharedCheck_329_ == 0)
{
v___x_319_ = v_x_314_;
v_isShared_320_ = v_isSharedCheck_329_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_tail_317_);
lean_inc(v_value_316_);
lean_inc(v_key_315_);
lean_dec(v_x_314_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_329_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
uint8_t v___x_321_; 
v___x_321_ = l_Lean_ExprStructEq_beq(v_key_315_, v_a_312_);
if (v___x_321_ == 0)
{
lean_object* v___x_322_; lean_object* v___x_324_; 
v___x_322_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__2___redArg(v_a_312_, v_b_313_, v_tail_317_);
if (v_isShared_320_ == 0)
{
lean_ctor_set(v___x_319_, 2, v___x_322_);
v___x_324_ = v___x_319_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v_key_315_);
lean_ctor_set(v_reuseFailAlloc_325_, 1, v_value_316_);
lean_ctor_set(v_reuseFailAlloc_325_, 2, v___x_322_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
return v___x_324_;
}
}
else
{
lean_object* v___x_327_; 
lean_dec(v_value_316_);
lean_dec(v_key_315_);
if (v_isShared_320_ == 0)
{
lean_ctor_set(v___x_319_, 1, v_b_313_);
lean_ctor_set(v___x_319_, 0, v_a_312_);
v___x_327_ = v___x_319_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v_a_312_);
lean_ctor_set(v_reuseFailAlloc_328_, 1, v_b_313_);
lean_ctor_set(v_reuseFailAlloc_328_, 2, v_tail_317_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
return v___x_327_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0___redArg(lean_object* v_m_330_, lean_object* v_a_331_, lean_object* v_b_332_){
_start:
{
lean_object* v_size_333_; lean_object* v_buckets_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_377_; 
v_size_333_ = lean_ctor_get(v_m_330_, 0);
v_buckets_334_ = lean_ctor_get(v_m_330_, 1);
v_isSharedCheck_377_ = !lean_is_exclusive(v_m_330_);
if (v_isSharedCheck_377_ == 0)
{
v___x_336_ = v_m_330_;
v_isShared_337_ = v_isSharedCheck_377_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_buckets_334_);
lean_inc(v_size_333_);
lean_dec(v_m_330_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_377_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v___x_338_; uint64_t v___x_339_; uint64_t v___x_340_; uint64_t v___x_341_; uint64_t v_fold_342_; uint64_t v___x_343_; uint64_t v___x_344_; uint64_t v___x_345_; size_t v___x_346_; size_t v___x_347_; size_t v___x_348_; size_t v___x_349_; size_t v___x_350_; lean_object* v_bkt_351_; uint8_t v___x_352_; 
v___x_338_ = lean_array_get_size(v_buckets_334_);
v___x_339_ = l_Lean_ExprStructEq_hash(v_a_331_);
v___x_340_ = 32ULL;
v___x_341_ = lean_uint64_shift_right(v___x_339_, v___x_340_);
v_fold_342_ = lean_uint64_xor(v___x_339_, v___x_341_);
v___x_343_ = 16ULL;
v___x_344_ = lean_uint64_shift_right(v_fold_342_, v___x_343_);
v___x_345_ = lean_uint64_xor(v_fold_342_, v___x_344_);
v___x_346_ = lean_uint64_to_usize(v___x_345_);
v___x_347_ = lean_usize_of_nat(v___x_338_);
v___x_348_ = ((size_t)1ULL);
v___x_349_ = lean_usize_sub(v___x_347_, v___x_348_);
v___x_350_ = lean_usize_land(v___x_346_, v___x_349_);
v_bkt_351_ = lean_array_uget_borrowed(v_buckets_334_, v___x_350_);
v___x_352_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__0___redArg(v_a_331_, v_bkt_351_);
if (v___x_352_ == 0)
{
lean_object* v___x_353_; lean_object* v_size_x27_354_; lean_object* v___x_355_; lean_object* v_buckets_x27_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; uint8_t v___x_362_; 
v___x_353_ = lean_unsigned_to_nat(1u);
v_size_x27_354_ = lean_nat_add(v_size_333_, v___x_353_);
lean_dec(v_size_333_);
lean_inc(v_bkt_351_);
v___x_355_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_355_, 0, v_a_331_);
lean_ctor_set(v___x_355_, 1, v_b_332_);
lean_ctor_set(v___x_355_, 2, v_bkt_351_);
v_buckets_x27_356_ = lean_array_uset(v_buckets_334_, v___x_350_, v___x_355_);
v___x_357_ = lean_unsigned_to_nat(4u);
v___x_358_ = lean_nat_mul(v_size_x27_354_, v___x_357_);
v___x_359_ = lean_unsigned_to_nat(3u);
v___x_360_ = lean_nat_div(v___x_358_, v___x_359_);
lean_dec(v___x_358_);
v___x_361_ = lean_array_get_size(v_buckets_x27_356_);
v___x_362_ = lean_nat_dec_le(v___x_360_, v___x_361_);
lean_dec(v___x_360_);
if (v___x_362_ == 0)
{
lean_object* v_val_363_; lean_object* v___x_365_; 
v_val_363_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__1___redArg(v_buckets_x27_356_);
if (v_isShared_337_ == 0)
{
lean_ctor_set(v___x_336_, 1, v_val_363_);
lean_ctor_set(v___x_336_, 0, v_size_x27_354_);
v___x_365_ = v___x_336_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v_size_x27_354_);
lean_ctor_set(v_reuseFailAlloc_366_, 1, v_val_363_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
else
{
lean_object* v___x_368_; 
if (v_isShared_337_ == 0)
{
lean_ctor_set(v___x_336_, 1, v_buckets_x27_356_);
lean_ctor_set(v___x_336_, 0, v_size_x27_354_);
v___x_368_ = v___x_336_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v_size_x27_354_);
lean_ctor_set(v_reuseFailAlloc_369_, 1, v_buckets_x27_356_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
}
else
{
lean_object* v___x_370_; lean_object* v_buckets_x27_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_375_; 
lean_inc(v_bkt_351_);
v___x_370_ = lean_box(0);
v_buckets_x27_371_ = lean_array_uset(v_buckets_334_, v___x_350_, v___x_370_);
v___x_372_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__2___redArg(v_a_331_, v_b_332_, v_bkt_351_);
v___x_373_ = lean_array_uset(v_buckets_x27_371_, v___x_350_, v___x_372_);
if (v_isShared_337_ == 0)
{
lean_ctor_set(v___x_336_, 1, v___x_373_);
v___x_375_ = v___x_336_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v_size_333_);
lean_ctor_set(v_reuseFailAlloc_376_, 1, v___x_373_);
v___x_375_ = v_reuseFailAlloc_376_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
return v___x_375_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1_spec__4___redArg(lean_object* v_a_378_, lean_object* v_x_379_){
_start:
{
if (lean_obj_tag(v_x_379_) == 0)
{
lean_object* v___x_380_; 
v___x_380_ = lean_box(0);
return v___x_380_;
}
else
{
lean_object* v_key_381_; lean_object* v_value_382_; lean_object* v_tail_383_; uint8_t v___x_384_; 
v_key_381_ = lean_ctor_get(v_x_379_, 0);
v_value_382_ = lean_ctor_get(v_x_379_, 1);
v_tail_383_ = lean_ctor_get(v_x_379_, 2);
v___x_384_ = l_Lean_ExprStructEq_beq(v_key_381_, v_a_378_);
if (v___x_384_ == 0)
{
v_x_379_ = v_tail_383_;
goto _start;
}
else
{
lean_object* v___x_386_; 
lean_inc(v_value_382_);
v___x_386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_386_, 0, v_value_382_);
return v___x_386_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1_spec__4___redArg___boxed(lean_object* v_a_387_, lean_object* v_x_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1_spec__4___redArg(v_a_387_, v_x_388_);
lean_dec(v_x_388_);
lean_dec_ref(v_a_387_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1___redArg(lean_object* v_m_390_, lean_object* v_a_391_){
_start:
{
lean_object* v_buckets_392_; lean_object* v___x_393_; uint64_t v___x_394_; uint64_t v___x_395_; uint64_t v___x_396_; uint64_t v_fold_397_; uint64_t v___x_398_; uint64_t v___x_399_; uint64_t v___x_400_; size_t v___x_401_; size_t v___x_402_; size_t v___x_403_; size_t v___x_404_; size_t v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v_buckets_392_ = lean_ctor_get(v_m_390_, 1);
v___x_393_ = lean_array_get_size(v_buckets_392_);
v___x_394_ = l_Lean_ExprStructEq_hash(v_a_391_);
v___x_395_ = 32ULL;
v___x_396_ = lean_uint64_shift_right(v___x_394_, v___x_395_);
v_fold_397_ = lean_uint64_xor(v___x_394_, v___x_396_);
v___x_398_ = 16ULL;
v___x_399_ = lean_uint64_shift_right(v_fold_397_, v___x_398_);
v___x_400_ = lean_uint64_xor(v_fold_397_, v___x_399_);
v___x_401_ = lean_uint64_to_usize(v___x_400_);
v___x_402_ = lean_usize_of_nat(v___x_393_);
v___x_403_ = ((size_t)1ULL);
v___x_404_ = lean_usize_sub(v___x_402_, v___x_403_);
v___x_405_ = lean_usize_land(v___x_401_, v___x_404_);
v___x_406_ = lean_array_uget_borrowed(v_buckets_392_, v___x_405_);
v___x_407_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1_spec__4___redArg(v_a_391_, v___x_406_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1___redArg___boxed(lean_object* v_m_408_, lean_object* v_a_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1___redArg(v_m_408_, v_a_409_);
lean_dec_ref(v_a_409_);
lean_dec_ref(v_m_408_);
return v_res_410_;
}
}
static lean_object* _init_l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___closed__2(void){
_start:
{
lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_413_ = ((lean_object*)(l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___closed__1));
v___x_414_ = lean_unsigned_to_nat(10u);
v___x_415_ = lean_unsigned_to_nat(72u);
v___x_416_ = ((lean_object*)(l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___closed__0));
v___x_417_ = ((lean_object*)(l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope___closed__0));
v___x_418_ = l_mkPanicMessageWithDecl(v___x_417_, v___x_416_, v___x_415_, v___x_414_, v___x_413_);
return v___x_418_;
}
}
lean_object* l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go(lean_object* v_e_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_){
_start:
{
lean_object* v_a_426_; lean_object* v_fst_427_; lean_object* v___y_433_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_436_ = lean_box(0);
v___x_437_ = lean_st_ref_get(v_a_420_);
v___x_438_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1___redArg(v___x_437_, v_e_419_);
lean_dec(v___x_437_);
if (lean_obj_tag(v___x_438_) == 0)
{
lean_object* v___x_439_; lean_object* v___x_440_; uint8_t v___x_441_; 
v___x_439_ = ((lean_object*)(l_Lean_Expr_hasBinderNameHint___lam__0___closed__1));
v___x_440_ = lean_unsigned_to_nat(6u);
v___x_441_ = l_Lean_Expr_isAppOfArity(v_e_419_, v___x_439_, v___x_440_);
if (v___x_441_ == 0)
{
switch(lean_obj_tag(v_e_419_))
{
case 7:
{
lean_object* v_binderName_442_; lean_object* v_binderType_443_; lean_object* v_body_444_; uint8_t v_binderInfo_445_; lean_object* v___x_446_; 
v_binderName_442_ = lean_ctor_get(v_e_419_, 0);
v_binderType_443_ = lean_ctor_get(v_e_419_, 1);
v_body_444_ = lean_ctor_get(v_e_419_, 2);
v_binderInfo_445_ = lean_ctor_get_uint8(v_e_419_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_443_);
v___x_446_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go(v_binderType_443_, v_a_420_, v_a_421_, v_a_422_, v_a_423_);
if (lean_obj_tag(v___x_446_) == 0)
{
lean_object* v_a_447_; lean_object* v_fst_448_; lean_object* v_snd_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
v_a_447_ = lean_ctor_get(v___x_446_, 0);
lean_inc(v_a_447_);
lean_dec_ref_known(v___x_446_, 1);
v_fst_448_ = lean_ctor_get(v_a_447_, 0);
lean_inc(v_fst_448_);
v_snd_449_ = lean_ctor_get(v_a_447_, 1);
lean_inc(v_snd_449_);
lean_dec(v_a_447_);
lean_inc(v_binderName_442_);
v___x_450_ = lean_array_push(v_snd_449_, v_binderName_442_);
lean_inc_ref(v_body_444_);
v___x_451_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go(v_body_444_, v_a_420_, v___x_450_, v_a_422_, v_a_423_);
if (lean_obj_tag(v___x_451_) == 0)
{
lean_object* v_a_452_; lean_object* v_fst_453_; lean_object* v_snd_454_; lean_object* v___x_455_; lean_object* v_fst_456_; lean_object* v_snd_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_465_; 
v_a_452_ = lean_ctor_get(v___x_451_, 0);
lean_inc(v_a_452_);
lean_dec_ref_known(v___x_451_, 1);
v_fst_453_ = lean_ctor_get(v_a_452_, 0);
lean_inc(v_fst_453_);
v_snd_454_ = lean_ctor_get(v_a_452_, 1);
lean_inc(v_snd_454_);
lean_dec(v_a_452_);
v___x_455_ = l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope(v_snd_454_);
v_fst_456_ = lean_ctor_get(v___x_455_, 0);
v_snd_457_ = lean_ctor_get(v___x_455_, 1);
v_isSharedCheck_465_ = !lean_is_exclusive(v___x_455_);
if (v_isSharedCheck_465_ == 0)
{
v___x_459_ = v___x_455_;
v_isShared_460_ = v_isSharedCheck_465_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_snd_457_);
lean_inc(v_fst_456_);
lean_dec(v___x_455_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_465_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_461_; lean_object* v___x_463_; 
v___x_461_ = l_Lean_Expr_forallE___override(v_fst_456_, v_fst_448_, v_fst_453_, v_binderInfo_445_);
lean_inc_ref(v___x_461_);
if (v_isShared_460_ == 0)
{
lean_ctor_set(v___x_459_, 0, v___x_461_);
v___x_463_ = v___x_459_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v___x_461_);
lean_ctor_set(v_reuseFailAlloc_464_, 1, v_snd_457_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
v_a_426_ = v___x_463_;
v_fst_427_ = v___x_461_;
goto v___jp_425_;
}
}
}
else
{
lean_dec(v_fst_448_);
v___y_433_ = v___x_451_;
goto v___jp_432_;
}
}
else
{
v___y_433_ = v___x_446_;
goto v___jp_432_;
}
}
case 6:
{
lean_object* v_binderName_466_; lean_object* v_binderType_467_; lean_object* v_body_468_; uint8_t v_binderInfo_469_; lean_object* v___x_470_; 
v_binderName_466_ = lean_ctor_get(v_e_419_, 0);
v_binderType_467_ = lean_ctor_get(v_e_419_, 1);
v_body_468_ = lean_ctor_get(v_e_419_, 2);
v_binderInfo_469_ = lean_ctor_get_uint8(v_e_419_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_467_);
v___x_470_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go(v_binderType_467_, v_a_420_, v_a_421_, v_a_422_, v_a_423_);
if (lean_obj_tag(v___x_470_) == 0)
{
lean_object* v_a_471_; lean_object* v_fst_472_; lean_object* v_snd_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
v_a_471_ = lean_ctor_get(v___x_470_, 0);
lean_inc(v_a_471_);
lean_dec_ref_known(v___x_470_, 1);
v_fst_472_ = lean_ctor_get(v_a_471_, 0);
lean_inc(v_fst_472_);
v_snd_473_ = lean_ctor_get(v_a_471_, 1);
lean_inc(v_snd_473_);
lean_dec(v_a_471_);
lean_inc(v_binderName_466_);
v___x_474_ = lean_array_push(v_snd_473_, v_binderName_466_);
lean_inc_ref(v_body_468_);
v___x_475_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go(v_body_468_, v_a_420_, v___x_474_, v_a_422_, v_a_423_);
if (lean_obj_tag(v___x_475_) == 0)
{
lean_object* v_a_476_; lean_object* v_fst_477_; lean_object* v_snd_478_; lean_object* v___x_479_; lean_object* v_fst_480_; lean_object* v_snd_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_489_; 
v_a_476_ = lean_ctor_get(v___x_475_, 0);
lean_inc(v_a_476_);
lean_dec_ref_known(v___x_475_, 1);
v_fst_477_ = lean_ctor_get(v_a_476_, 0);
lean_inc(v_fst_477_);
v_snd_478_ = lean_ctor_get(v_a_476_, 1);
lean_inc(v_snd_478_);
lean_dec(v_a_476_);
v___x_479_ = l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope(v_snd_478_);
v_fst_480_ = lean_ctor_get(v___x_479_, 0);
v_snd_481_ = lean_ctor_get(v___x_479_, 1);
v_isSharedCheck_489_ = !lean_is_exclusive(v___x_479_);
if (v_isSharedCheck_489_ == 0)
{
v___x_483_ = v___x_479_;
v_isShared_484_ = v_isSharedCheck_489_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_snd_481_);
lean_inc(v_fst_480_);
lean_dec(v___x_479_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_489_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_485_; lean_object* v___x_487_; 
v___x_485_ = l_Lean_Expr_lam___override(v_fst_480_, v_fst_472_, v_fst_477_, v_binderInfo_469_);
lean_inc_ref(v___x_485_);
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 0, v___x_485_);
v___x_487_ = v___x_483_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v___x_485_);
lean_ctor_set(v_reuseFailAlloc_488_, 1, v_snd_481_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
v_a_426_ = v___x_487_;
v_fst_427_ = v___x_485_;
goto v___jp_425_;
}
}
}
else
{
lean_dec(v_fst_472_);
v___y_433_ = v___x_475_;
goto v___jp_432_;
}
}
else
{
v___y_433_ = v___x_470_;
goto v___jp_432_;
}
}
case 8:
{
lean_object* v_declName_490_; lean_object* v_type_491_; lean_object* v_value_492_; lean_object* v_body_493_; uint8_t v_nondep_494_; lean_object* v___x_495_; 
v_declName_490_ = lean_ctor_get(v_e_419_, 0);
v_type_491_ = lean_ctor_get(v_e_419_, 1);
v_value_492_ = lean_ctor_get(v_e_419_, 2);
v_body_493_ = lean_ctor_get(v_e_419_, 3);
v_nondep_494_ = lean_ctor_get_uint8(v_e_419_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_491_);
v___x_495_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go(v_type_491_, v_a_420_, v_a_421_, v_a_422_, v_a_423_);
if (lean_obj_tag(v___x_495_) == 0)
{
lean_object* v_a_496_; lean_object* v_fst_497_; lean_object* v_snd_498_; lean_object* v___x_499_; 
v_a_496_ = lean_ctor_get(v___x_495_, 0);
lean_inc(v_a_496_);
lean_dec_ref_known(v___x_495_, 1);
v_fst_497_ = lean_ctor_get(v_a_496_, 0);
lean_inc(v_fst_497_);
v_snd_498_ = lean_ctor_get(v_a_496_, 1);
lean_inc(v_snd_498_);
lean_dec(v_a_496_);
lean_inc_ref(v_value_492_);
v___x_499_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go(v_value_492_, v_a_420_, v_snd_498_, v_a_422_, v_a_423_);
if (lean_obj_tag(v___x_499_) == 0)
{
lean_object* v_a_500_; lean_object* v_fst_501_; lean_object* v_snd_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
v_a_500_ = lean_ctor_get(v___x_499_, 0);
lean_inc(v_a_500_);
lean_dec_ref_known(v___x_499_, 1);
v_fst_501_ = lean_ctor_get(v_a_500_, 0);
lean_inc(v_fst_501_);
v_snd_502_ = lean_ctor_get(v_a_500_, 1);
lean_inc(v_snd_502_);
lean_dec(v_a_500_);
lean_inc(v_declName_490_);
v___x_503_ = lean_array_push(v_snd_502_, v_declName_490_);
lean_inc_ref(v_body_493_);
v___x_504_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go(v_body_493_, v_a_420_, v___x_503_, v_a_422_, v_a_423_);
if (lean_obj_tag(v___x_504_) == 0)
{
lean_object* v_a_505_; lean_object* v_fst_506_; lean_object* v_snd_507_; lean_object* v___x_508_; lean_object* v_fst_509_; lean_object* v_snd_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_518_; 
v_a_505_ = lean_ctor_get(v___x_504_, 0);
lean_inc(v_a_505_);
lean_dec_ref_known(v___x_504_, 1);
v_fst_506_ = lean_ctor_get(v_a_505_, 0);
lean_inc(v_fst_506_);
v_snd_507_ = lean_ctor_get(v_a_505_, 1);
lean_inc(v_snd_507_);
lean_dec(v_a_505_);
v___x_508_ = l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope(v_snd_507_);
v_fst_509_ = lean_ctor_get(v___x_508_, 0);
v_snd_510_ = lean_ctor_get(v___x_508_, 1);
v_isSharedCheck_518_ = !lean_is_exclusive(v___x_508_);
if (v_isSharedCheck_518_ == 0)
{
v___x_512_ = v___x_508_;
v_isShared_513_ = v_isSharedCheck_518_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_snd_510_);
lean_inc(v_fst_509_);
lean_dec(v___x_508_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_518_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_514_; lean_object* v___x_516_; 
v___x_514_ = l_Lean_Expr_letE___override(v_fst_509_, v_fst_497_, v_fst_501_, v_fst_506_, v_nondep_494_);
lean_inc_ref(v___x_514_);
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 0, v___x_514_);
v___x_516_ = v___x_512_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v___x_514_);
lean_ctor_set(v_reuseFailAlloc_517_, 1, v_snd_510_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
v_a_426_ = v___x_516_;
v_fst_427_ = v___x_514_;
goto v___jp_425_;
}
}
}
else
{
lean_dec(v_fst_501_);
lean_dec(v_fst_497_);
v___y_433_ = v___x_504_;
goto v___jp_432_;
}
}
else
{
lean_dec(v_fst_497_);
v___y_433_ = v___x_499_;
goto v___jp_432_;
}
}
else
{
v___y_433_ = v___x_495_;
goto v___jp_432_;
}
}
case 5:
{
lean_object* v_fn_519_; lean_object* v_arg_520_; lean_object* v___x_521_; 
v_fn_519_ = lean_ctor_get(v_e_419_, 0);
v_arg_520_ = lean_ctor_get(v_e_419_, 1);
lean_inc_ref(v_fn_519_);
v___x_521_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go(v_fn_519_, v_a_420_, v_a_421_, v_a_422_, v_a_423_);
if (lean_obj_tag(v___x_521_) == 0)
{
lean_object* v_a_522_; lean_object* v_fst_523_; lean_object* v_snd_524_; lean_object* v___x_525_; 
v_a_522_ = lean_ctor_get(v___x_521_, 0);
lean_inc(v_a_522_);
lean_dec_ref_known(v___x_521_, 1);
v_fst_523_ = lean_ctor_get(v_a_522_, 0);
lean_inc(v_fst_523_);
v_snd_524_ = lean_ctor_get(v_a_522_, 1);
lean_inc(v_snd_524_);
lean_dec(v_a_522_);
lean_inc_ref(v_arg_520_);
v___x_525_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go(v_arg_520_, v_a_420_, v_snd_524_, v_a_422_, v_a_423_);
if (lean_obj_tag(v___x_525_) == 0)
{
lean_object* v_a_526_; lean_object* v_fst_527_; lean_object* v_snd_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_545_; 
v_a_526_ = lean_ctor_get(v___x_525_, 0);
lean_inc(v_a_526_);
lean_dec_ref_known(v___x_525_, 1);
v_fst_527_ = lean_ctor_get(v_a_526_, 0);
v_snd_528_ = lean_ctor_get(v_a_526_, 1);
v_isSharedCheck_545_ = !lean_is_exclusive(v_a_526_);
if (v_isSharedCheck_545_ == 0)
{
v___x_530_ = v_a_526_;
v_isShared_531_ = v_isSharedCheck_545_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_snd_528_);
lean_inc(v_fst_527_);
lean_dec(v_a_526_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_545_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___y_533_; size_t v___x_537_; size_t v___x_538_; uint8_t v___x_539_; 
v___x_537_ = lean_ptr_addr(v_fn_519_);
v___x_538_ = lean_ptr_addr(v_fst_523_);
v___x_539_ = lean_usize_dec_eq(v___x_537_, v___x_538_);
if (v___x_539_ == 0)
{
lean_object* v___x_540_; 
v___x_540_ = l_Lean_Expr_app___override(v_fst_523_, v_fst_527_);
v___y_533_ = v___x_540_;
goto v___jp_532_;
}
else
{
size_t v___x_541_; size_t v___x_542_; uint8_t v___x_543_; 
v___x_541_ = lean_ptr_addr(v_arg_520_);
v___x_542_ = lean_ptr_addr(v_fst_527_);
v___x_543_ = lean_usize_dec_eq(v___x_541_, v___x_542_);
if (v___x_543_ == 0)
{
lean_object* v___x_544_; 
v___x_544_ = l_Lean_Expr_app___override(v_fst_523_, v_fst_527_);
v___y_533_ = v___x_544_;
goto v___jp_532_;
}
else
{
lean_dec(v_fst_527_);
lean_dec(v_fst_523_);
lean_inc_ref(v_e_419_);
v___y_533_ = v_e_419_;
goto v___jp_532_;
}
}
v___jp_532_:
{
lean_object* v___x_535_; 
lean_inc_ref(v___y_533_);
if (v_isShared_531_ == 0)
{
lean_ctor_set(v___x_530_, 0, v___y_533_);
v___x_535_ = v___x_530_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v___y_533_);
lean_ctor_set(v_reuseFailAlloc_536_, 1, v_snd_528_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
v_a_426_ = v___x_535_;
v_fst_427_ = v___y_533_;
goto v___jp_425_;
}
}
}
}
else
{
lean_dec(v_fst_523_);
v___y_433_ = v___x_525_;
goto v___jp_432_;
}
}
else
{
v___y_433_ = v___x_521_;
goto v___jp_432_;
}
}
case 10:
{
lean_object* v_data_546_; lean_object* v_expr_547_; lean_object* v___x_548_; 
v_data_546_ = lean_ctor_get(v_e_419_, 0);
v_expr_547_ = lean_ctor_get(v_e_419_, 1);
lean_inc_ref(v_expr_547_);
v___x_548_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go(v_expr_547_, v_a_420_, v_a_421_, v_a_422_, v_a_423_);
if (lean_obj_tag(v___x_548_) == 0)
{
lean_object* v_a_549_; lean_object* v_fst_550_; lean_object* v_snd_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_564_; 
v_a_549_ = lean_ctor_get(v___x_548_, 0);
lean_inc(v_a_549_);
lean_dec_ref_known(v___x_548_, 1);
v_fst_550_ = lean_ctor_get(v_a_549_, 0);
v_snd_551_ = lean_ctor_get(v_a_549_, 1);
v_isSharedCheck_564_ = !lean_is_exclusive(v_a_549_);
if (v_isSharedCheck_564_ == 0)
{
v___x_553_ = v_a_549_;
v_isShared_554_ = v_isSharedCheck_564_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_snd_551_);
lean_inc(v_fst_550_);
lean_dec(v_a_549_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_564_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v___y_556_; size_t v___x_560_; size_t v___x_561_; uint8_t v___x_562_; 
v___x_560_ = lean_ptr_addr(v_expr_547_);
v___x_561_ = lean_ptr_addr(v_fst_550_);
v___x_562_ = lean_usize_dec_eq(v___x_560_, v___x_561_);
if (v___x_562_ == 0)
{
lean_object* v___x_563_; 
lean_inc(v_data_546_);
v___x_563_ = l_Lean_Expr_mdata___override(v_data_546_, v_fst_550_);
v___y_556_ = v___x_563_;
goto v___jp_555_;
}
else
{
lean_dec(v_fst_550_);
lean_inc_ref(v_e_419_);
v___y_556_ = v_e_419_;
goto v___jp_555_;
}
v___jp_555_:
{
lean_object* v___x_558_; 
lean_inc_ref(v___y_556_);
if (v_isShared_554_ == 0)
{
lean_ctor_set(v___x_553_, 0, v___y_556_);
v___x_558_ = v___x_553_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v___y_556_);
lean_ctor_set(v_reuseFailAlloc_559_, 1, v_snd_551_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
v_a_426_ = v___x_558_;
v_fst_427_ = v___y_556_;
goto v___jp_425_;
}
}
}
}
else
{
v___y_433_ = v___x_548_;
goto v___jp_432_;
}
}
case 11:
{
lean_object* v_typeName_565_; lean_object* v_idx_566_; lean_object* v_struct_567_; lean_object* v___x_568_; 
v_typeName_565_ = lean_ctor_get(v_e_419_, 0);
v_idx_566_ = lean_ctor_get(v_e_419_, 1);
v_struct_567_ = lean_ctor_get(v_e_419_, 2);
lean_inc_ref(v_struct_567_);
v___x_568_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go(v_struct_567_, v_a_420_, v_a_421_, v_a_422_, v_a_423_);
if (lean_obj_tag(v___x_568_) == 0)
{
lean_object* v_a_569_; lean_object* v_fst_570_; lean_object* v_snd_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_584_; 
v_a_569_ = lean_ctor_get(v___x_568_, 0);
lean_inc(v_a_569_);
lean_dec_ref_known(v___x_568_, 1);
v_fst_570_ = lean_ctor_get(v_a_569_, 0);
v_snd_571_ = lean_ctor_get(v_a_569_, 1);
v_isSharedCheck_584_ = !lean_is_exclusive(v_a_569_);
if (v_isSharedCheck_584_ == 0)
{
v___x_573_ = v_a_569_;
v_isShared_574_ = v_isSharedCheck_584_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_snd_571_);
lean_inc(v_fst_570_);
lean_dec(v_a_569_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_584_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___y_576_; size_t v___x_580_; size_t v___x_581_; uint8_t v___x_582_; 
v___x_580_ = lean_ptr_addr(v_struct_567_);
v___x_581_ = lean_ptr_addr(v_fst_570_);
v___x_582_ = lean_usize_dec_eq(v___x_580_, v___x_581_);
if (v___x_582_ == 0)
{
lean_object* v___x_583_; 
lean_inc(v_idx_566_);
lean_inc(v_typeName_565_);
v___x_583_ = l_Lean_Expr_proj___override(v_typeName_565_, v_idx_566_, v_fst_570_);
v___y_576_ = v___x_583_;
goto v___jp_575_;
}
else
{
lean_dec(v_fst_570_);
lean_inc_ref(v_e_419_);
v___y_576_ = v_e_419_;
goto v___jp_575_;
}
v___jp_575_:
{
lean_object* v___x_578_; 
lean_inc_ref(v___y_576_);
if (v_isShared_574_ == 0)
{
lean_ctor_set(v___x_573_, 0, v___y_576_);
v___x_578_ = v___x_573_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v___y_576_);
lean_ctor_set(v_reuseFailAlloc_579_, 1, v_snd_571_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
v_a_426_ = v___x_578_;
v_fst_427_ = v___y_576_;
goto v___jp_425_;
}
}
}
}
else
{
v___y_433_ = v___x_568_;
goto v___jp_432_;
}
}
default: 
{
lean_object* v___x_585_; 
lean_inc_ref_n(v_e_419_, 2);
v___x_585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_585_, 0, v_e_419_);
lean_ctor_set(v___x_585_, 1, v_a_421_);
v_a_426_ = v___x_585_;
v_fst_427_ = v_e_419_;
goto v___jp_425_;
}
}
}
else
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v_v_588_; lean_object* v_b_589_; lean_object* v_e_590_; lean_object* v___x_591_; 
v___x_586_ = l_Lean_Expr_appFn_x21(v_e_419_);
v___x_587_ = l_Lean_Expr_appFn_x21(v___x_586_);
v_v_588_ = l_Lean_Expr_appArg_x21(v___x_587_);
lean_dec_ref(v___x_587_);
v_b_589_ = l_Lean_Expr_appArg_x21(v___x_586_);
lean_dec_ref(v___x_586_);
v_e_590_ = l_Lean_Expr_appArg_x21(v_e_419_);
v___x_591_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go(v_e_590_, v_a_420_, v_a_421_, v_a_422_, v_a_423_);
if (lean_obj_tag(v___x_591_) == 0)
{
lean_object* v_a_592_; lean_object* v_fst_593_; lean_object* v_snd_594_; lean_object* v___f_595_; 
v_a_592_ = lean_ctor_get(v___x_591_, 0);
lean_inc(v_a_592_);
lean_dec_ref_known(v___x_591_, 1);
v_fst_593_ = lean_ctor_get(v_a_592_, 0);
lean_inc_n(v_fst_593_, 2);
v_snd_594_ = lean_ctor_get(v_a_592_, 1);
lean_inc(v_snd_594_);
lean_dec(v_a_592_);
v___f_595_ = lean_alloc_closure((void*)(l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___lam__0___boxed), 7, 1);
lean_closure_set(v___f_595_, 0, v_fst_593_);
if (lean_obj_tag(v_v_588_) == 0)
{
lean_object* v_deBruijnIndex_596_; lean_object* v___x_597_; 
v_deBruijnIndex_596_ = lean_ctor_get(v_v_588_, 0);
lean_inc(v_deBruijnIndex_596_);
lean_dec_ref_known(v_v_588_, 1);
v___x_597_ = l_Lean_Expr_headBeta(v_b_589_);
switch(lean_obj_tag(v___x_597_))
{
case 6:
{
lean_object* v_binderName_598_; lean_object* v_binderType_599_; lean_object* v_body_600_; uint8_t v_binderInfo_601_; lean_object* v___x_602_; 
lean_dec(v_fst_593_);
v_binderName_598_ = lean_ctor_get(v___x_597_, 0);
lean_inc(v_binderName_598_);
v_binderType_599_ = lean_ctor_get(v___x_597_, 1);
lean_inc_ref(v_binderType_599_);
v_body_600_ = lean_ctor_get(v___x_597_, 2);
lean_inc_ref(v_body_600_);
v_binderInfo_601_ = lean_ctor_get_uint8(v___x_597_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v___x_597_, 3);
v___x_602_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___lam__1(v___f_595_, v_deBruijnIndex_596_, v_binderName_598_, v_binderType_599_, v_body_600_, v_binderInfo_601_, v_a_420_, v_snd_594_, v_a_422_, v_a_423_);
lean_dec_ref(v_body_600_);
lean_dec_ref(v_binderType_599_);
lean_dec(v_deBruijnIndex_596_);
v___y_433_ = v___x_602_;
goto v___jp_432_;
}
case 7:
{
lean_object* v_binderName_603_; lean_object* v_binderType_604_; lean_object* v_body_605_; uint8_t v_binderInfo_606_; lean_object* v___x_607_; 
lean_dec(v_fst_593_);
v_binderName_603_ = lean_ctor_get(v___x_597_, 0);
lean_inc(v_binderName_603_);
v_binderType_604_ = lean_ctor_get(v___x_597_, 1);
lean_inc_ref(v_binderType_604_);
v_body_605_ = lean_ctor_get(v___x_597_, 2);
lean_inc_ref(v_body_605_);
v_binderInfo_606_ = lean_ctor_get_uint8(v___x_597_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v___x_597_, 3);
v___x_607_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___lam__1(v___f_595_, v_deBruijnIndex_596_, v_binderName_603_, v_binderType_604_, v_body_605_, v_binderInfo_606_, v_a_420_, v_snd_594_, v_a_422_, v_a_423_);
lean_dec_ref(v_body_605_);
lean_dec_ref(v_binderType_604_);
lean_dec(v_deBruijnIndex_596_);
v___y_433_ = v___x_607_;
goto v___jp_432_;
}
default: 
{
lean_object* v___x_608_; uint8_t v___x_609_; 
lean_dec_ref(v___x_597_);
lean_dec_ref(v___f_595_);
v___x_608_ = lean_array_get_size(v_snd_594_);
v___x_609_ = lean_nat_dec_lt(v_deBruijnIndex_596_, v___x_608_);
if (v___x_609_ == 0)
{
lean_object* v___x_610_; lean_object* v___x_611_; 
lean_dec(v_deBruijnIndex_596_);
lean_dec(v_fst_593_);
v___x_610_ = lean_obj_once(&l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___closed__2, &l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___closed__2_once, _init_l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___closed__2);
v___x_611_ = l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2(v___x_610_, v_a_420_, v_snd_594_, v_a_422_, v_a_423_);
v___y_433_ = v___x_611_;
goto v___jp_432_;
}
else
{
lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_612_ = lean_nat_sub(v___x_608_, v_deBruijnIndex_596_);
v___x_613_ = lean_unsigned_to_nat(1u);
v___x_614_ = lean_nat_sub(v___x_612_, v___x_613_);
lean_dec(v___x_612_);
v___x_615_ = lean_array_get_borrowed(v___x_436_, v_snd_594_, v___x_614_);
lean_dec(v___x_614_);
lean_inc(v___x_615_);
v___x_616_ = l_Lean_Core_mkFreshUserName(v___x_615_, v_a_422_, v_a_423_);
if (lean_obj_tag(v___x_616_) == 0)
{
lean_object* v_a_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v_a_617_ = lean_ctor_get(v___x_616_, 0);
lean_inc(v_a_617_);
lean_dec_ref_known(v___x_616_, 1);
v___x_618_ = lean_box(0);
v___x_619_ = l___private_Lean_Meta_BinderNameHint_0__Lean_rememberName(v_deBruijnIndex_596_, v_a_617_, v_snd_594_);
lean_dec(v_deBruijnIndex_596_);
v___x_620_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___lam__0(v_fst_593_, v___x_618_, v_a_420_, v___x_619_, v_a_422_, v_a_423_);
v___y_433_ = v___x_620_;
goto v___jp_432_;
}
else
{
lean_object* v_a_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_628_; 
lean_dec(v_deBruijnIndex_596_);
lean_dec(v_snd_594_);
lean_dec(v_fst_593_);
lean_dec_ref(v_e_419_);
v_a_621_ = lean_ctor_get(v___x_616_, 0);
v_isSharedCheck_628_ = !lean_is_exclusive(v___x_616_);
if (v_isSharedCheck_628_ == 0)
{
v___x_623_ = v___x_616_;
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_a_621_);
lean_dec(v___x_616_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v___x_626_; 
if (v_isShared_624_ == 0)
{
v___x_626_ = v___x_623_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_a_621_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_629_; lean_object* v___x_630_; 
lean_dec_ref(v___f_595_);
lean_dec_ref(v_b_589_);
lean_dec_ref(v_v_588_);
v___x_629_ = lean_box(0);
v___x_630_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___lam__0(v_fst_593_, v___x_629_, v_a_420_, v_snd_594_, v_a_422_, v_a_423_);
v___y_433_ = v___x_630_;
goto v___jp_432_;
}
}
else
{
lean_dec_ref(v_b_589_);
lean_dec_ref(v_v_588_);
v___y_433_ = v___x_591_;
goto v___jp_432_;
}
}
}
else
{
lean_object* v_val_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_639_; 
lean_dec_ref(v_e_419_);
v_val_631_ = lean_ctor_get(v___x_438_, 0);
v_isSharedCheck_639_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_639_ == 0)
{
v___x_633_ = v___x_438_;
v_isShared_634_ = v_isSharedCheck_639_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_val_631_);
lean_dec(v___x_438_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_639_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v___x_635_; lean_object* v___x_637_; 
v___x_635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_635_, 0, v_val_631_);
lean_ctor_set(v___x_635_, 1, v_a_421_);
if (v_isShared_634_ == 0)
{
lean_ctor_set_tag(v___x_633_, 0);
lean_ctor_set(v___x_633_, 0, v___x_635_);
v___x_637_ = v___x_633_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v___x_635_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
}
v___jp_425_:
{
lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_428_ = lean_st_ref_take(v_a_420_);
v___x_429_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0___redArg(v___x_428_, v_e_419_, v_fst_427_);
v___x_430_ = lean_st_ref_put(v_a_420_, v___x_429_);
v___x_431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_431_, 0, v_a_426_);
return v___x_431_;
}
v___jp_432_:
{
if (lean_obj_tag(v___y_433_) == 0)
{
lean_object* v_a_434_; lean_object* v_fst_435_; 
v_a_434_ = lean_ctor_get(v___y_433_, 0);
lean_inc(v_a_434_);
lean_dec_ref_known(v___y_433_, 1);
v_fst_435_ = lean_ctor_get(v_a_434_, 0);
lean_inc(v_fst_435_);
v_a_426_ = v_a_434_;
v_fst_427_ = v_fst_435_;
goto v___jp_425_;
}
else
{
lean_dec_ref(v_e_419_);
return v___y_433_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_419_ = stack[0].m_obj;
lean_object* v_a_420_ = stack[1].m_obj;
lean_object* v_a_421_ = stack[2].m_obj;
lean_object* v_a_422_ = stack[3].m_obj;
lean_object* v_a_423_ = stack[4].m_obj;
lean_object* v_res_640_;
v_res_640_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go(v_e_419_, v_a_420_, v_a_421_, v_a_422_, v_a_423_);
stack->m_obj
 = v_res_640_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___boxed(lean_object* v_e_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go(v_e_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_);
lean_dec(v_a_645_);
lean_dec_ref(v_a_644_);
lean_dec(v_a_642_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0(lean_object* v_00_u03b2_648_, lean_object* v_m_649_, lean_object* v_a_650_, lean_object* v_b_651_){
_start:
{
lean_object* v___x_652_; 
v___x_652_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0___redArg(v_m_649_, v_a_650_, v_b_651_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1(lean_object* v_00_u03b2_653_, lean_object* v_m_654_, lean_object* v_a_655_){
_start:
{
lean_object* v___x_656_; 
v___x_656_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1___redArg(v_m_654_, v_a_655_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1___boxed(lean_object* v_00_u03b2_657_, lean_object* v_m_658_, lean_object* v_a_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1(v_00_u03b2_657_, v_m_658_, v_a_659_);
lean_dec_ref(v_a_659_);
lean_dec_ref(v_m_658_);
return v_res_660_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__0(lean_object* v_00_u03b2_661_, lean_object* v_a_662_, lean_object* v_x_663_){
_start:
{
uint8_t v___x_664_; 
v___x_664_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__0___redArg(v_a_662_, v_x_663_);
return v___x_664_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_662_ = stack[1].m_obj;
lean_object* v_x_663_ = stack[2].m_obj;
uint8_t v_res_665_;
v_res_665_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__0(lean_box(0), v_a_662_, v_x_663_);
stack->m_num = v_res_665_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_666_, lean_object* v_a_667_, lean_object* v_x_668_){
_start:
{
uint8_t v_res_669_; lean_object* v_r_670_; 
v_res_669_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__0(v_00_u03b2_666_, v_a_667_, v_x_668_);
lean_dec(v_x_668_);
lean_dec_ref(v_a_667_);
v_r_670_ = lean_box(v_res_669_);
return v_r_670_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__1(lean_object* v_00_u03b2_671_, lean_object* v_data_672_){
_start:
{
lean_object* v___x_673_; 
v___x_673_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__1___redArg(v_data_672_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__2(lean_object* v_00_u03b2_674_, lean_object* v_a_675_, lean_object* v_b_676_, lean_object* v_x_677_){
_start:
{
lean_object* v___x_678_; 
v___x_678_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__2___redArg(v_a_675_, v_b_676_, v_x_677_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1_spec__4(lean_object* v_00_u03b2_679_, lean_object* v_a_680_, lean_object* v_x_681_){
_start:
{
lean_object* v___x_682_; 
v___x_682_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1_spec__4___redArg(v_a_680_, v_x_681_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1_spec__4___boxed(lean_object* v_00_u03b2_683_, lean_object* v_a_684_, lean_object* v_x_685_){
_start:
{
lean_object* v_res_686_; 
v_res_686_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1_spec__4(v_00_u03b2_683_, v_a_684_, v_x_685_);
lean_dec(v_x_685_);
lean_dec_ref(v_a_684_);
return v_res_686_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_687_, lean_object* v_i_688_, lean_object* v_source_689_, lean_object* v_target_690_){
_start:
{
lean_object* v___x_691_; 
v___x_691_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__1_spec__3___redArg(v_i_688_, v_source_689_, v_target_690_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_692_, lean_object* v_x_693_, lean_object* v_x_694_){
_start:
{
lean_object* v___x_695_; 
v___x_695_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__1_spec__3_spec__5___redArg(v_x_693_, v_x_694_);
return v___x_695_;
}
}
static lean_object* _init_l_Lean_Expr_resolveBinderNameHint___closed__0(void){
_start:
{
lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_696_ = lean_box(0);
v___x_697_ = lean_unsigned_to_nat(16u);
v___x_698_ = lean_mk_array(v___x_697_, v___x_696_);
return v___x_698_;
}
}
static lean_object* _init_l_Lean_Expr_resolveBinderNameHint___closed__1(void){
_start:
{
lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_699_ = lean_obj_once(&l_Lean_Expr_resolveBinderNameHint___closed__0, &l_Lean_Expr_resolveBinderNameHint___closed__0_once, _init_l_Lean_Expr_resolveBinderNameHint___closed__0);
v___x_700_ = lean_unsigned_to_nat(0u);
v___x_701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_701_, 0, v___x_700_);
lean_ctor_set(v___x_701_, 1, v___x_699_);
return v___x_701_;
}
}
lean_object* l_Lean_Expr_resolveBinderNameHint(lean_object* v_e_704_, lean_object* v_a_705_, lean_object* v_a_706_){
_start:
{
lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_708_ = lean_obj_once(&l_Lean_Expr_resolveBinderNameHint___closed__1, &l_Lean_Expr_resolveBinderNameHint___closed__1_once, _init_l_Lean_Expr_resolveBinderNameHint___closed__1);
v___x_709_ = ((lean_object*)(l_Lean_Expr_resolveBinderNameHint___closed__2));
v___x_710_ = lean_st_mk_ref(v___x_708_);
v___x_711_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go(v_e_704_, v___x_710_, v___x_709_, v_a_705_, v_a_706_);
if (lean_obj_tag(v___x_711_) == 0)
{
lean_object* v_a_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_721_; 
v_a_712_ = lean_ctor_get(v___x_711_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_711_);
if (v_isSharedCheck_721_ == 0)
{
v___x_714_ = v___x_711_;
v_isShared_715_ = v_isSharedCheck_721_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_a_712_);
lean_dec(v___x_711_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_721_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v_fst_716_; lean_object* v___x_717_; lean_object* v___x_719_; 
v_fst_716_ = lean_ctor_get(v_a_712_, 0);
lean_inc(v_fst_716_);
lean_dec(v_a_712_);
v___x_717_ = lean_st_ref_get(v___x_710_);
lean_dec(v___x_710_);
lean_dec(v___x_717_);
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 0, v_fst_716_);
v___x_719_ = v___x_714_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_fst_716_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
}
else
{
lean_object* v_a_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_729_; 
lean_dec(v___x_710_);
v_a_722_ = lean_ctor_get(v___x_711_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_711_);
if (v_isSharedCheck_729_ == 0)
{
v___x_724_ = v___x_711_;
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_a_722_);
lean_dec(v___x_711_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_727_; 
if (v_isShared_725_ == 0)
{
v___x_727_ = v___x_724_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_a_722_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_resolveBinderNameHint_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_704_ = stack[0].m_obj;
lean_object* v_a_705_ = stack[1].m_obj;
lean_object* v_a_706_ = stack[2].m_obj;
lean_object* v_res_730_;
v_res_730_ = l_Lean_Expr_resolveBinderNameHint(v_e_704_, v_a_705_, v_a_706_);
stack->m_obj
 = v_res_730_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_resolveBinderNameHint___boxed(lean_object* v_e_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l_Lean_Expr_resolveBinderNameHint(v_e_731_, v_a_732_, v_a_733_);
lean_dec(v_a_733_);
lean_dec_ref(v_a_732_);
return v_res_735_;
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
