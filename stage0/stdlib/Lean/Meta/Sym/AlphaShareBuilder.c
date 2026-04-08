// Lean compiler output
// Module: Lean.Meta.Sym.AlphaShareBuilder
// Imports: public import Lean.Meta.Sym.SymM
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash___boxed(lean_object*);
lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instInhabitedSymM(lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_lit___override(lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* l_Lean_Meta_Sym_isDebugEnabled___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_read___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonOfMonadLift___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonOfMonadLift___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonOfMonadLift(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "__dummy__"};
static const lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy___closed__0_value),LEAN_SCALAR_PTR_LITERAL(182, 141, 137, 132, 208, 124, 31, 129)}};
static const lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg(lean_object*, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Sym_share1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0(lean_object*, lean_object*, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lean.Meta.Sym.AlphaShareBuilder"};
static const lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0_value;
static const lean_string_object l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Lean.Meta.Sym.Internal.Sym.assertShared"};
static const lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__1_value;
static const lean_string_object l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "assertion violation: isSameExpr prev.expr e\n\n"};
static const lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Sym_Internal_instMonadShareCommonSymM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Internal_Sym_share1___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonSymM___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Internal_instMonadShareCommonSymM___closed__0_value;
static const lean_closure_object l_Lean_Meta_Sym_Internal_instMonadShareCommonSymM___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Internal_Sym_assertShared___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonSymM___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Internal_instMonadShareCommonSymM___closed__1_value;
static const lean_closure_object l_Lean_Meta_Sym_Internal_instMonadShareCommonSymM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_isDebugEnabled___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonSymM___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Internal_instMonadShareCommonSymM___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Sym_Internal_instMonadShareCommonSymM___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Internal_instMonadShareCommonSymM___closed__0_value),((lean_object*)&l_Lean_Meta_Sym_Internal_instMonadShareCommonSymM___closed__1_value),((lean_object*)&l_Lean_Meta_Sym_Internal_instMonadShareCommonSymM___closed__2_value)}};
static const lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonSymM___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_Internal_instMonadShareCommonSymM___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonSymM = (const lean_object*)&l_Lean_Meta_Sym_Internal_instMonadShareCommonSymM___closed__3_value;
static const lean_closure_object l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__0_value;
static const lean_closure_object l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_share1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_share1(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_share1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__0 = (const lean_object*)&l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__0_value;
static const lean_closure_object l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__1 = (const lean_object*)&l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__2 = (const lean_object*)&l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__3 = (const lean_object*)&l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__4 = (const lean_object*)&l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__4_value;
static const lean_closure_object l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__5 = (const lean_object*)&l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__5_value;
static const lean_closure_object l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__6 = (const lean_object*)&l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__6_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "Lean.Meta.Sym.Internal.Builder.assertShared"};
static const lean_object* l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__0_value;
static const lean_string_object l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 121, .m_capacity = 121, .m_length = 116, .m_data = "assertion violation: ( __do_lift._@.Lean.Meta.Sym.AlphaShareBuilder.3401574005._hygCtx._hyg.9.0 ).set.contains ⟨e⟩\n\n"};
static const lean_object* l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_assertShared(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_assertShared___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Internal_Builder_share1___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__0_value;
static const lean_closure_object l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Internal_Builder_assertShared___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLitS___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLitS(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMVarS___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMVarS(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkHaveS___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkHaveS___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkHaveS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_updateAppS_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.Expr.updateAppS!"};
static const lean_object* l_Lean_Expr_updateAppS_x21___redArg___closed__0 = (const lean_object*)&l_Lean_Expr_updateAppS_x21___redArg___closed__0_value;
static const lean_string_object l_Lean_Expr_updateAppS_x21___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "application expected"};
static const lean_object* l_Lean_Expr_updateAppS_x21___redArg___closed__1 = (const lean_object*)&l_Lean_Expr_updateAppS_x21___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Expr_updateAppS_x21___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_updateAppS_x21___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_updateAppS_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_updateAppS_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_updateMDataS_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Expr.updateMDataS!"};
static const lean_object* l_Lean_Expr_updateMDataS_x21___redArg___closed__0 = (const lean_object*)&l_Lean_Expr_updateMDataS_x21___redArg___closed__0_value;
static const lean_string_object l_Lean_Expr_updateMDataS_x21___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "mdata expected"};
static const lean_object* l_Lean_Expr_updateMDataS_x21___redArg___closed__1 = (const lean_object*)&l_Lean_Expr_updateMDataS_x21___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Expr_updateMDataS_x21___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_updateMDataS_x21___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_updateMDataS_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_updateMDataS_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_updateProjS_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.Expr.updateProjS!"};
static const lean_object* l_Lean_Expr_updateProjS_x21___redArg___closed__0 = (const lean_object*)&l_Lean_Expr_updateProjS_x21___redArg___closed__0_value;
static const lean_string_object l_Lean_Expr_updateProjS_x21___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "proj expected"};
static const lean_object* l_Lean_Expr_updateProjS_x21___redArg___closed__1 = (const lean_object*)&l_Lean_Expr_updateProjS_x21___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Expr_updateProjS_x21___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_updateProjS_x21___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_updateProjS_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_updateProjS_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_updateForallS_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.Expr.updateForallS!"};
static const lean_object* l_Lean_Expr_updateForallS_x21___redArg___closed__0 = (const lean_object*)&l_Lean_Expr_updateForallS_x21___redArg___closed__0_value;
static const lean_string_object l_Lean_Expr_updateForallS_x21___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "forall expected"};
static const lean_object* l_Lean_Expr_updateForallS_x21___redArg___closed__1 = (const lean_object*)&l_Lean_Expr_updateForallS_x21___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Expr_updateForallS_x21___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_updateForallS_x21___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallS_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallS_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_updateLambdaS_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.Expr.updateLambdaS!"};
static const lean_object* l_Lean_Expr_updateLambdaS_x21___redArg___closed__0 = (const lean_object*)&l_Lean_Expr_updateLambdaS_x21___redArg___closed__0_value;
static const lean_string_object l_Lean_Expr_updateLambdaS_x21___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "lambda expected"};
static const lean_object* l_Lean_Expr_updateLambdaS_x21___redArg___closed__1 = (const lean_object*)&l_Lean_Expr_updateLambdaS_x21___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Expr_updateLambdaS_x21___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_updateLambdaS_x21___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_updateLambdaS_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_updateLambdaS_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_updateLetS_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.Expr.updateLetS!"};
static const lean_object* l_Lean_Expr_updateLetS_x21___redArg___closed__0 = (const lean_object*)&l_Lean_Expr_updateLetS_x21___redArg___closed__0_value;
static const lean_string_object l_Lean_Expr_updateLetS_x21___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "let expression expected"};
static const lean_object* l_Lean_Expr_updateLetS_x21___redArg___closed__1 = (const lean_object*)&l_Lean_Expr_updateLetS_x21___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Expr_updateLetS_x21___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_updateLetS_x21___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_updateLetS_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_updateLetS_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2085___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2085___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2085(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2086___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2086___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2086(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2087___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2087___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2087(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2088___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2088___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2088(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2089___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2089___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2089(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2080___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2080___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2080(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2081___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2081___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2081(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRangeS___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRangeS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevRangeS___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevRangeS___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevRangeS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevRangeS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevS___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonOfMonadLift___redArg___lam__0(lean_object* v_share1_1_, lean_object* v_inst_2_, lean_object* v_e_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = lean_apply_1(v_share1_1_, v_e_3_);
v___x_5_ = lean_apply_2(v_inst_2_, lean_box(0), v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonOfMonadLift___redArg___lam__1(lean_object* v_assertShared_6_, lean_object* v_inst_7_, lean_object* v_e_8_){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_9_ = lean_apply_1(v_assertShared_6_, v_e_8_);
v___x_10_ = lean_apply_2(v_inst_7_, lean_box(0), v___x_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonOfMonadLift___redArg(lean_object* v_inst_11_, lean_object* v_inst_12_){
_start:
{
lean_object* v_share1_13_; lean_object* v_assertShared_14_; lean_object* v_isDebugEnabled_15_; lean_object* v___x_17_; uint8_t v_isShared_18_; uint8_t v_isSharedCheck_25_; 
v_share1_13_ = lean_ctor_get(v_inst_12_, 0);
v_assertShared_14_ = lean_ctor_get(v_inst_12_, 1);
v_isDebugEnabled_15_ = lean_ctor_get(v_inst_12_, 2);
v_isSharedCheck_25_ = !lean_is_exclusive(v_inst_12_);
if (v_isSharedCheck_25_ == 0)
{
v___x_17_ = v_inst_12_;
v_isShared_18_ = v_isSharedCheck_25_;
goto v_resetjp_16_;
}
else
{
lean_inc(v_isDebugEnabled_15_);
lean_inc(v_assertShared_14_);
lean_inc(v_share1_13_);
lean_dec(v_inst_12_);
v___x_17_ = lean_box(0);
v_isShared_18_ = v_isSharedCheck_25_;
goto v_resetjp_16_;
}
v_resetjp_16_:
{
lean_object* v___f_19_; lean_object* v___f_20_; lean_object* v___x_21_; lean_object* v___x_23_; 
lean_inc_n(v_inst_11_, 2);
v___f_19_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_instMonadShareCommonOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_19_, 0, v_share1_13_);
lean_closure_set(v___f_19_, 1, v_inst_11_);
v___f_20_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_instMonadShareCommonOfMonadLift___redArg___lam__1), 3, 2);
lean_closure_set(v___f_20_, 0, v_assertShared_14_);
lean_closure_set(v___f_20_, 1, v_inst_11_);
v___x_21_ = lean_apply_2(v_inst_11_, lean_box(0), v_isDebugEnabled_15_);
if (v_isShared_18_ == 0)
{
lean_ctor_set(v___x_17_, 2, v___x_21_);
lean_ctor_set(v___x_17_, 1, v___f_20_);
lean_ctor_set(v___x_17_, 0, v___f_19_);
v___x_23_ = v___x_17_;
goto v_reusejp_22_;
}
else
{
lean_object* v_reuseFailAlloc_24_; 
v_reuseFailAlloc_24_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_24_, 0, v___f_19_);
lean_ctor_set(v_reuseFailAlloc_24_, 1, v___f_20_);
lean_ctor_set(v_reuseFailAlloc_24_, 2, v___x_21_);
v___x_23_ = v_reuseFailAlloc_24_;
goto v_reusejp_22_;
}
v_reusejp_22_:
{
return v___x_23_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonOfMonadLift(lean_object* v_m_26_, lean_object* v_n_27_, lean_object* v_inst_28_, lean_object* v_inst_29_){
_start:
{
lean_object* v_share1_30_; lean_object* v_assertShared_31_; lean_object* v_isDebugEnabled_32_; lean_object* v___x_34_; uint8_t v_isShared_35_; uint8_t v_isSharedCheck_42_; 
v_share1_30_ = lean_ctor_get(v_inst_29_, 0);
v_assertShared_31_ = lean_ctor_get(v_inst_29_, 1);
v_isDebugEnabled_32_ = lean_ctor_get(v_inst_29_, 2);
v_isSharedCheck_42_ = !lean_is_exclusive(v_inst_29_);
if (v_isSharedCheck_42_ == 0)
{
v___x_34_ = v_inst_29_;
v_isShared_35_ = v_isSharedCheck_42_;
goto v_resetjp_33_;
}
else
{
lean_inc(v_isDebugEnabled_32_);
lean_inc(v_assertShared_31_);
lean_inc(v_share1_30_);
lean_dec(v_inst_29_);
v___x_34_ = lean_box(0);
v_isShared_35_ = v_isSharedCheck_42_;
goto v_resetjp_33_;
}
v_resetjp_33_:
{
lean_object* v___f_36_; lean_object* v___f_37_; lean_object* v___x_38_; lean_object* v___x_40_; 
lean_inc_n(v_inst_28_, 2);
v___f_36_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_instMonadShareCommonOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_36_, 0, v_share1_30_);
lean_closure_set(v___f_36_, 1, v_inst_28_);
v___f_37_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_instMonadShareCommonOfMonadLift___redArg___lam__1), 3, 2);
lean_closure_set(v___f_37_, 0, v_assertShared_31_);
lean_closure_set(v___f_37_, 1, v_inst_28_);
v___x_38_ = lean_apply_2(v_inst_28_, lean_box(0), v_isDebugEnabled_32_);
if (v_isShared_35_ == 0)
{
lean_ctor_set(v___x_34_, 2, v___x_38_);
lean_ctor_set(v___x_34_, 1, v___f_37_);
lean_ctor_set(v___x_34_, 0, v___f_36_);
v___x_40_ = v___x_34_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_41_; 
v_reuseFailAlloc_41_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_41_, 0, v___f_36_);
lean_ctor_set(v_reuseFailAlloc_41_, 1, v___f_37_);
lean_ctor_set(v_reuseFailAlloc_41_, 2, v___x_38_);
v___x_40_ = v_reuseFailAlloc_41_;
goto v_reusejp_39_;
}
v_reusejp_39_:
{
return v___x_40_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy___closed__2(void){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_46_ = lean_box(0);
v___x_47_ = ((lean_object*)(l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy___closed__1));
v___x_48_ = l_Lean_mkConst(v___x_47_, v___x_46_);
return v___x_48_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy(void){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = lean_obj_once(&l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy___closed__2, &l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy___closed__2_once, _init_l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy___closed__2);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_x_50_, lean_object* v_x_51_, lean_object* v_x_52_, lean_object* v_x_53_){
_start:
{
lean_object* v_ks_54_; lean_object* v_vs_55_; lean_object* v___x_57_; uint8_t v_isShared_58_; uint8_t v_isSharedCheck_79_; 
v_ks_54_ = lean_ctor_get(v_x_50_, 0);
v_vs_55_ = lean_ctor_get(v_x_50_, 1);
v_isSharedCheck_79_ = !lean_is_exclusive(v_x_50_);
if (v_isSharedCheck_79_ == 0)
{
v___x_57_ = v_x_50_;
v_isShared_58_ = v_isSharedCheck_79_;
goto v_resetjp_56_;
}
else
{
lean_inc(v_vs_55_);
lean_inc(v_ks_54_);
lean_dec(v_x_50_);
v___x_57_ = lean_box(0);
v_isShared_58_ = v_isSharedCheck_79_;
goto v_resetjp_56_;
}
v_resetjp_56_:
{
lean_object* v___x_59_; uint8_t v___x_60_; 
v___x_59_ = lean_array_get_size(v_ks_54_);
v___x_60_ = lean_nat_dec_lt(v_x_51_, v___x_59_);
if (v___x_60_ == 0)
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_64_; 
lean_dec(v_x_51_);
v___x_61_ = lean_array_push(v_ks_54_, v_x_52_);
v___x_62_ = lean_array_push(v_vs_55_, v_x_53_);
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 1, v___x_62_);
lean_ctor_set(v___x_57_, 0, v___x_61_);
v___x_64_ = v___x_57_;
goto v_reusejp_63_;
}
else
{
lean_object* v_reuseFailAlloc_65_; 
v_reuseFailAlloc_65_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_65_, 0, v___x_61_);
lean_ctor_set(v_reuseFailAlloc_65_, 1, v___x_62_);
v___x_64_ = v_reuseFailAlloc_65_;
goto v_reusejp_63_;
}
v_reusejp_63_:
{
return v___x_64_;
}
}
else
{
lean_object* v_k_x27_66_; uint8_t v___x_67_; 
v_k_x27_66_ = lean_array_fget_borrowed(v_ks_54_, v_x_51_);
lean_inc(v_k_x27_66_);
lean_inc_ref(v_x_52_);
v___x_67_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_52_, v_k_x27_66_);
if (v___x_67_ == 0)
{
lean_object* v___x_69_; 
if (v_isShared_58_ == 0)
{
v___x_69_ = v___x_57_;
goto v_reusejp_68_;
}
else
{
lean_object* v_reuseFailAlloc_73_; 
v_reuseFailAlloc_73_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_73_, 0, v_ks_54_);
lean_ctor_set(v_reuseFailAlloc_73_, 1, v_vs_55_);
v___x_69_ = v_reuseFailAlloc_73_;
goto v_reusejp_68_;
}
v_reusejp_68_:
{
lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_70_ = lean_unsigned_to_nat(1u);
v___x_71_ = lean_nat_add(v_x_51_, v___x_70_);
lean_dec(v_x_51_);
v_x_50_ = v___x_69_;
v_x_51_ = v___x_71_;
goto _start;
}
}
else
{
lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_77_; 
v___x_74_ = lean_array_fset(v_ks_54_, v_x_51_, v_x_52_);
v___x_75_ = lean_array_fset(v_vs_55_, v_x_51_, v_x_53_);
lean_dec(v_x_51_);
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 1, v___x_75_);
lean_ctor_set(v___x_57_, 0, v___x_74_);
v___x_77_ = v___x_57_;
goto v_reusejp_76_;
}
else
{
lean_object* v_reuseFailAlloc_78_; 
v_reuseFailAlloc_78_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_78_, 0, v___x_74_);
lean_ctor_set(v_reuseFailAlloc_78_, 1, v___x_75_);
v___x_77_ = v_reuseFailAlloc_78_;
goto v_reusejp_76_;
}
v_reusejp_76_:
{
return v___x_77_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__3___redArg(lean_object* v_n_80_, lean_object* v_k_81_, lean_object* v_v_82_){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_83_ = lean_unsigned_to_nat(0u);
v___x_84_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__3_spec__4___redArg(v_n_80_, v___x_83_, v_k_81_, v_v_82_);
return v___x_84_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__0(void){
_start:
{
size_t v___x_85_; size_t v___x_86_; size_t v___x_87_; 
v___x_85_ = ((size_t)5ULL);
v___x_86_ = ((size_t)1ULL);
v___x_87_ = lean_usize_shift_left(v___x_86_, v___x_85_);
return v___x_87_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_88_; size_t v___x_89_; size_t v___x_90_; 
v___x_88_ = ((size_t)1ULL);
v___x_89_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__0);
v___x_90_ = lean_usize_sub(v___x_89_, v___x_88_);
return v___x_90_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg(lean_object* v_x_92_, size_t v_x_93_, size_t v_x_94_, lean_object* v_x_95_, lean_object* v_x_96_){
_start:
{
if (lean_obj_tag(v_x_92_) == 0)
{
lean_object* v_es_97_; size_t v___x_98_; size_t v___x_99_; size_t v___x_100_; size_t v___x_101_; lean_object* v_j_102_; lean_object* v___x_103_; uint8_t v___x_104_; 
v_es_97_ = lean_ctor_get(v_x_92_, 0);
v___x_98_ = ((size_t)5ULL);
v___x_99_ = ((size_t)1ULL);
v___x_100_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__1);
v___x_101_ = lean_usize_land(v_x_93_, v___x_100_);
v_j_102_ = lean_usize_to_nat(v___x_101_);
v___x_103_ = lean_array_get_size(v_es_97_);
v___x_104_ = lean_nat_dec_lt(v_j_102_, v___x_103_);
if (v___x_104_ == 0)
{
lean_dec(v_j_102_);
lean_dec(v_x_96_);
lean_dec_ref(v_x_95_);
return v_x_92_;
}
else
{
lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_141_; 
lean_inc_ref(v_es_97_);
v_isSharedCheck_141_ = !lean_is_exclusive(v_x_92_);
if (v_isSharedCheck_141_ == 0)
{
lean_object* v_unused_142_; 
v_unused_142_ = lean_ctor_get(v_x_92_, 0);
lean_dec(v_unused_142_);
v___x_106_ = v_x_92_;
v_isShared_107_ = v_isSharedCheck_141_;
goto v_resetjp_105_;
}
else
{
lean_dec(v_x_92_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_141_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
lean_object* v_v_108_; lean_object* v___x_109_; lean_object* v_xs_x27_110_; lean_object* v___y_112_; 
v_v_108_ = lean_array_fget(v_es_97_, v_j_102_);
v___x_109_ = lean_box(0);
v_xs_x27_110_ = lean_array_fset(v_es_97_, v_j_102_, v___x_109_);
switch(lean_obj_tag(v_v_108_))
{
case 0:
{
lean_object* v_key_117_; lean_object* v_val_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_128_; 
v_key_117_ = lean_ctor_get(v_v_108_, 0);
v_val_118_ = lean_ctor_get(v_v_108_, 1);
v_isSharedCheck_128_ = !lean_is_exclusive(v_v_108_);
if (v_isSharedCheck_128_ == 0)
{
v___x_120_ = v_v_108_;
v_isShared_121_ = v_isSharedCheck_128_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_val_118_);
lean_inc(v_key_117_);
lean_dec(v_v_108_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_128_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
uint8_t v___x_122_; 
lean_inc(v_key_117_);
lean_inc_ref(v_x_95_);
v___x_122_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_95_, v_key_117_);
if (v___x_122_ == 0)
{
lean_object* v___x_123_; lean_object* v___x_124_; 
lean_del_object(v___x_120_);
v___x_123_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_117_, v_val_118_, v_x_95_, v_x_96_);
v___x_124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_124_, 0, v___x_123_);
v___y_112_ = v___x_124_;
goto v___jp_111_;
}
else
{
lean_object* v___x_126_; 
lean_dec(v_val_118_);
lean_dec(v_key_117_);
if (v_isShared_121_ == 0)
{
lean_ctor_set(v___x_120_, 1, v_x_96_);
lean_ctor_set(v___x_120_, 0, v_x_95_);
v___x_126_ = v___x_120_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v_x_95_);
lean_ctor_set(v_reuseFailAlloc_127_, 1, v_x_96_);
v___x_126_ = v_reuseFailAlloc_127_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
v___y_112_ = v___x_126_;
goto v___jp_111_;
}
}
}
}
case 1:
{
lean_object* v_node_129_; lean_object* v___x_131_; uint8_t v_isShared_132_; uint8_t v_isSharedCheck_139_; 
v_node_129_ = lean_ctor_get(v_v_108_, 0);
v_isSharedCheck_139_ = !lean_is_exclusive(v_v_108_);
if (v_isSharedCheck_139_ == 0)
{
v___x_131_ = v_v_108_;
v_isShared_132_ = v_isSharedCheck_139_;
goto v_resetjp_130_;
}
else
{
lean_inc(v_node_129_);
lean_dec(v_v_108_);
v___x_131_ = lean_box(0);
v_isShared_132_ = v_isSharedCheck_139_;
goto v_resetjp_130_;
}
v_resetjp_130_:
{
size_t v___x_133_; size_t v___x_134_; lean_object* v___x_135_; lean_object* v___x_137_; 
v___x_133_ = lean_usize_shift_right(v_x_93_, v___x_98_);
v___x_134_ = lean_usize_add(v_x_94_, v___x_99_);
v___x_135_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg(v_node_129_, v___x_133_, v___x_134_, v_x_95_, v_x_96_);
if (v_isShared_132_ == 0)
{
lean_ctor_set(v___x_131_, 0, v___x_135_);
v___x_137_ = v___x_131_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v___x_135_);
v___x_137_ = v_reuseFailAlloc_138_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
v___y_112_ = v___x_137_;
goto v___jp_111_;
}
}
}
default: 
{
lean_object* v___x_140_; 
v___x_140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_140_, 0, v_x_95_);
lean_ctor_set(v___x_140_, 1, v_x_96_);
v___y_112_ = v___x_140_;
goto v___jp_111_;
}
}
v___jp_111_:
{
lean_object* v___x_113_; lean_object* v___x_115_; 
v___x_113_ = lean_array_fset(v_xs_x27_110_, v_j_102_, v___y_112_);
lean_dec(v_j_102_);
if (v_isShared_107_ == 0)
{
lean_ctor_set(v___x_106_, 0, v___x_113_);
v___x_115_ = v___x_106_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v___x_113_);
v___x_115_ = v_reuseFailAlloc_116_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
return v___x_115_;
}
}
}
}
}
else
{
lean_object* v_ks_143_; lean_object* v_vs_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_164_; 
v_ks_143_ = lean_ctor_get(v_x_92_, 0);
v_vs_144_ = lean_ctor_get(v_x_92_, 1);
v_isSharedCheck_164_ = !lean_is_exclusive(v_x_92_);
if (v_isSharedCheck_164_ == 0)
{
v___x_146_ = v_x_92_;
v_isShared_147_ = v_isSharedCheck_164_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_vs_144_);
lean_inc(v_ks_143_);
lean_dec(v_x_92_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_164_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v___x_149_; 
if (v_isShared_147_ == 0)
{
v___x_149_ = v___x_146_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v_ks_143_);
lean_ctor_set(v_reuseFailAlloc_163_, 1, v_vs_144_);
v___x_149_ = v_reuseFailAlloc_163_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
lean_object* v_newNode_150_; uint8_t v___y_152_; size_t v___x_158_; uint8_t v___x_159_; 
v_newNode_150_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__3___redArg(v___x_149_, v_x_95_, v_x_96_);
v___x_158_ = ((size_t)7ULL);
v___x_159_ = lean_usize_dec_le(v___x_158_, v_x_94_);
if (v___x_159_ == 0)
{
lean_object* v___x_160_; lean_object* v___x_161_; uint8_t v___x_162_; 
v___x_160_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_150_);
v___x_161_ = lean_unsigned_to_nat(4u);
v___x_162_ = lean_nat_dec_lt(v___x_160_, v___x_161_);
lean_dec(v___x_160_);
v___y_152_ = v___x_162_;
goto v___jp_151_;
}
else
{
v___y_152_ = v___x_159_;
goto v___jp_151_;
}
v___jp_151_:
{
if (v___y_152_ == 0)
{
lean_object* v_ks_153_; lean_object* v_vs_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v_ks_153_ = lean_ctor_get(v_newNode_150_, 0);
lean_inc_ref(v_ks_153_);
v_vs_154_ = lean_ctor_get(v_newNode_150_, 1);
lean_inc_ref(v_vs_154_);
lean_dec_ref(v_newNode_150_);
v___x_155_ = lean_unsigned_to_nat(0u);
v___x_156_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__2);
v___x_157_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4___redArg(v_x_94_, v_ks_153_, v_vs_154_, v___x_155_, v___x_156_);
lean_dec_ref(v_vs_154_);
lean_dec_ref(v_ks_153_);
return v___x_157_;
}
else
{
return v_newNode_150_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4___redArg(size_t v_depth_165_, lean_object* v_keys_166_, lean_object* v_vals_167_, lean_object* v_i_168_, lean_object* v_entries_169_){
_start:
{
lean_object* v___x_170_; uint8_t v___x_171_; 
v___x_170_ = lean_array_get_size(v_keys_166_);
v___x_171_ = lean_nat_dec_lt(v_i_168_, v___x_170_);
if (v___x_171_ == 0)
{
lean_dec(v_i_168_);
return v_entries_169_;
}
else
{
lean_object* v_k_172_; lean_object* v_v_173_; uint64_t v___x_174_; size_t v_h_175_; size_t v___x_176_; lean_object* v___x_177_; size_t v___x_178_; size_t v___x_179_; size_t v___x_180_; size_t v_h_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v_k_172_ = lean_array_fget_borrowed(v_keys_166_, v_i_168_);
v_v_173_ = lean_array_fget_borrowed(v_vals_167_, v_i_168_);
v___x_174_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_k_172_);
v_h_175_ = lean_uint64_to_usize(v___x_174_);
v___x_176_ = ((size_t)5ULL);
v___x_177_ = lean_unsigned_to_nat(1u);
v___x_178_ = ((size_t)1ULL);
v___x_179_ = lean_usize_sub(v_depth_165_, v___x_178_);
v___x_180_ = lean_usize_mul(v___x_176_, v___x_179_);
v_h_181_ = lean_usize_shift_right(v_h_175_, v___x_180_);
v___x_182_ = lean_nat_add(v_i_168_, v___x_177_);
lean_dec(v_i_168_);
lean_inc(v_v_173_);
lean_inc(v_k_172_);
v___x_183_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg(v_entries_169_, v_h_181_, v_depth_165_, v_k_172_, v_v_173_);
v_i_168_ = v___x_182_;
v_entries_169_ = v___x_183_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_depth_185_, lean_object* v_keys_186_, lean_object* v_vals_187_, lean_object* v_i_188_, lean_object* v_entries_189_){
_start:
{
size_t v_depth_boxed_190_; lean_object* v_res_191_; 
v_depth_boxed_190_ = lean_unbox_usize(v_depth_185_);
lean_dec(v_depth_185_);
v_res_191_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4___redArg(v_depth_boxed_190_, v_keys_186_, v_vals_187_, v_i_188_, v_entries_189_);
lean_dec_ref(v_vals_187_);
lean_dec_ref(v_keys_186_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___boxed(lean_object* v_x_192_, lean_object* v_x_193_, lean_object* v_x_194_, lean_object* v_x_195_, lean_object* v_x_196_){
_start:
{
size_t v_x_2171__boxed_197_; size_t v_x_2172__boxed_198_; lean_object* v_res_199_; 
v_x_2171__boxed_197_ = lean_unbox_usize(v_x_193_);
lean_dec(v_x_193_);
v_x_2172__boxed_198_ = lean_unbox_usize(v_x_194_);
lean_dec(v_x_194_);
v_res_199_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg(v_x_192_, v_x_2171__boxed_197_, v_x_2172__boxed_198_, v_x_195_, v_x_196_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1___redArg(lean_object* v_x_200_, lean_object* v_x_201_, lean_object* v_x_202_){
_start:
{
uint64_t v___x_203_; size_t v___x_204_; size_t v___x_205_; lean_object* v___x_206_; 
v___x_203_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_201_);
v___x_204_ = lean_uint64_to_usize(v___x_203_);
v___x_205_ = ((size_t)1ULL);
v___x_206_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg(v_x_200_, v___x_204_, v___x_205_, v_x_201_, v_x_202_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0___redArg(lean_object* v_keys_207_, lean_object* v_i_208_, lean_object* v_k_209_, lean_object* v_k_u2080_210_){
_start:
{
lean_object* v___x_211_; uint8_t v___x_212_; 
v___x_211_ = lean_array_get_size(v_keys_207_);
v___x_212_ = lean_nat_dec_lt(v_i_208_, v___x_211_);
if (v___x_212_ == 0)
{
lean_dec_ref(v_k_209_);
lean_dec(v_i_208_);
lean_inc_ref(v_k_u2080_210_);
return v_k_u2080_210_;
}
else
{
lean_object* v_k_x27_213_; uint8_t v___x_214_; 
v_k_x27_213_ = lean_array_fget_borrowed(v_keys_207_, v_i_208_);
lean_inc(v_k_x27_213_);
lean_inc_ref(v_k_209_);
v___x_214_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_k_209_, v_k_x27_213_);
if (v___x_214_ == 0)
{
lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_215_ = lean_unsigned_to_nat(1u);
v___x_216_ = lean_nat_add(v_i_208_, v___x_215_);
lean_dec(v_i_208_);
v_i_208_ = v___x_216_;
goto _start;
}
else
{
lean_dec_ref(v_k_209_);
lean_dec(v_i_208_);
lean_inc(v_k_x27_213_);
return v_k_x27_213_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0___redArg___boxed(lean_object* v_keys_218_, lean_object* v_i_219_, lean_object* v_k_220_, lean_object* v_k_u2080_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0___redArg(v_keys_218_, v_i_219_, v_k_220_, v_k_u2080_221_);
lean_dec_ref(v_k_u2080_221_);
lean_dec_ref(v_keys_218_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg(lean_object* v_x_223_, size_t v_x_224_, lean_object* v_x_225_, lean_object* v_x_226_){
_start:
{
if (lean_obj_tag(v_x_223_) == 0)
{
lean_object* v_es_227_; lean_object* v___x_228_; size_t v___x_229_; size_t v___x_230_; size_t v___x_231_; lean_object* v_j_232_; lean_object* v___x_233_; 
v_es_227_ = lean_ctor_get(v_x_223_, 0);
lean_inc_ref(v_es_227_);
lean_dec_ref(v_x_223_);
v___x_228_ = lean_box(2);
v___x_229_ = ((size_t)5ULL);
v___x_230_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__1);
v___x_231_ = lean_usize_land(v_x_224_, v___x_230_);
v_j_232_ = lean_usize_to_nat(v___x_231_);
v___x_233_ = lean_array_get(v___x_228_, v_es_227_, v_j_232_);
lean_dec(v_j_232_);
lean_dec_ref(v_es_227_);
switch(lean_obj_tag(v___x_233_))
{
case 0:
{
lean_object* v_key_234_; uint8_t v___x_235_; 
v_key_234_ = lean_ctor_get(v___x_233_, 0);
lean_inc_n(v_key_234_, 2);
lean_dec_ref(v___x_233_);
v___x_235_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_225_, v_key_234_);
if (v___x_235_ == 0)
{
lean_dec(v_key_234_);
lean_inc_ref(v_x_226_);
return v_x_226_;
}
else
{
return v_key_234_;
}
}
case 1:
{
lean_object* v_node_236_; size_t v___x_237_; 
v_node_236_ = lean_ctor_get(v___x_233_, 0);
lean_inc(v_node_236_);
lean_dec_ref(v___x_233_);
v___x_237_ = lean_usize_shift_right(v_x_224_, v___x_229_);
v_x_223_ = v_node_236_;
v_x_224_ = v___x_237_;
goto _start;
}
default: 
{
lean_dec_ref(v_x_225_);
lean_inc_ref(v_x_226_);
return v_x_226_;
}
}
}
else
{
lean_object* v_ks_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v_ks_239_ = lean_ctor_get(v_x_223_, 0);
lean_inc_ref(v_ks_239_);
lean_dec_ref(v_x_223_);
v___x_240_ = lean_unsigned_to_nat(0u);
v___x_241_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0___redArg(v_ks_239_, v___x_240_, v_x_225_, v_x_226_);
lean_dec_ref(v_ks_239_);
return v___x_241_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg___boxed(lean_object* v_x_242_, lean_object* v_x_243_, lean_object* v_x_244_, lean_object* v_x_245_){
_start:
{
size_t v_x_2365__boxed_246_; lean_object* v_res_247_; 
v_x_2365__boxed_246_ = lean_unbox_usize(v_x_243_);
lean_dec(v_x_243_);
v_res_247_ = l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg(v_x_242_, v_x_2365__boxed_246_, v_x_244_, v_x_245_);
lean_dec_ref(v_x_245_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object* v_e_248_, lean_object* v_a_249_){
_start:
{
lean_object* v___x_251_; lean_object* v_share_252_; lean_object* v___x_253_; uint64_t v___x_254_; size_t v___x_255_; lean_object* v___x_256_; uint8_t v___x_257_; 
v___x_251_ = lean_st_ref_get(v_a_249_);
v_share_252_ = lean_ctor_get(v___x_251_, 0);
lean_inc_ref(v_share_252_);
lean_dec(v___x_251_);
v___x_253_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy;
v___x_254_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_248_);
v___x_255_ = lean_uint64_to_usize(v___x_254_);
lean_inc_ref(v_e_248_);
v___x_256_ = l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg(v_share_252_, v___x_255_, v_e_248_, v___x_253_);
v___x_257_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_256_, v___x_253_);
if (v___x_257_ == 0)
{
lean_object* v___x_258_; 
lean_dec_ref(v_e_248_);
v___x_258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_258_, 0, v___x_256_);
return v___x_258_;
}
else
{
lean_object* v___x_259_; lean_object* v_share_260_; lean_object* v_maxFVar_261_; lean_object* v_proofInstInfo_262_; lean_object* v_inferType_263_; lean_object* v_getLevel_264_; lean_object* v_congrInfo_265_; lean_object* v_defEqI_266_; lean_object* v_extensions_267_; lean_object* v_issues_268_; lean_object* v_canon_269_; uint8_t v_debug_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_281_; 
lean_dec_ref(v___x_256_);
v___x_259_ = lean_st_ref_take(v_a_249_);
v_share_260_ = lean_ctor_get(v___x_259_, 0);
v_maxFVar_261_ = lean_ctor_get(v___x_259_, 1);
v_proofInstInfo_262_ = lean_ctor_get(v___x_259_, 2);
v_inferType_263_ = lean_ctor_get(v___x_259_, 3);
v_getLevel_264_ = lean_ctor_get(v___x_259_, 4);
v_congrInfo_265_ = lean_ctor_get(v___x_259_, 5);
v_defEqI_266_ = lean_ctor_get(v___x_259_, 6);
v_extensions_267_ = lean_ctor_get(v___x_259_, 7);
v_issues_268_ = lean_ctor_get(v___x_259_, 8);
v_canon_269_ = lean_ctor_get(v___x_259_, 9);
v_debug_270_ = lean_ctor_get_uint8(v___x_259_, sizeof(void*)*10);
v_isSharedCheck_281_ = !lean_is_exclusive(v___x_259_);
if (v_isSharedCheck_281_ == 0)
{
v___x_272_ = v___x_259_;
v_isShared_273_ = v_isSharedCheck_281_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_canon_269_);
lean_inc(v_issues_268_);
lean_inc(v_extensions_267_);
lean_inc(v_defEqI_266_);
lean_inc(v_congrInfo_265_);
lean_inc(v_getLevel_264_);
lean_inc(v_inferType_263_);
lean_inc(v_proofInstInfo_262_);
lean_inc(v_maxFVar_261_);
lean_inc(v_share_260_);
lean_dec(v___x_259_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_281_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_277_; 
v___x_274_ = lean_box(0);
lean_inc_ref(v_e_248_);
v___x_275_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1___redArg(v_share_260_, v_e_248_, v___x_274_);
if (v_isShared_273_ == 0)
{
lean_ctor_set(v___x_272_, 0, v___x_275_);
v___x_277_ = v___x_272_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v___x_275_);
lean_ctor_set(v_reuseFailAlloc_280_, 1, v_maxFVar_261_);
lean_ctor_set(v_reuseFailAlloc_280_, 2, v_proofInstInfo_262_);
lean_ctor_set(v_reuseFailAlloc_280_, 3, v_inferType_263_);
lean_ctor_set(v_reuseFailAlloc_280_, 4, v_getLevel_264_);
lean_ctor_set(v_reuseFailAlloc_280_, 5, v_congrInfo_265_);
lean_ctor_set(v_reuseFailAlloc_280_, 6, v_defEqI_266_);
lean_ctor_set(v_reuseFailAlloc_280_, 7, v_extensions_267_);
lean_ctor_set(v_reuseFailAlloc_280_, 8, v_issues_268_);
lean_ctor_set(v_reuseFailAlloc_280_, 9, v_canon_269_);
lean_ctor_set_uint8(v_reuseFailAlloc_280_, sizeof(void*)*10, v_debug_270_);
v___x_277_ = v_reuseFailAlloc_280_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_278_ = lean_st_ref_set(v_a_249_, v___x_277_);
v___x_279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_279_, 0, v_e_248_);
return v___x_279_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg___boxed(lean_object* v_e_282_, lean_object* v_a_283_, lean_object* v_a_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v_e_282_, v_a_283_);
lean_dec(v_a_283_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Sym_share1(lean_object* v_e_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_){
_start:
{
lean_object* v___x_294_; 
v___x_294_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v_e_286_, v_a_288_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___boxed(lean_object* v_e_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_Lean_Meta_Sym_Internal_Sym_share1(v_e_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_);
lean_dec(v_a_301_);
lean_dec_ref(v_a_300_);
lean_dec(v_a_299_);
lean_dec_ref(v_a_298_);
lean_dec(v_a_297_);
lean_dec_ref(v_a_296_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0(lean_object* v_00_u03b2_304_, lean_object* v_x_305_, size_t v_x_306_, lean_object* v_x_307_, lean_object* v_x_308_){
_start:
{
lean_object* v___x_309_; 
v___x_309_ = l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg(v_x_305_, v_x_306_, v_x_307_, v_x_308_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___boxed(lean_object* v_00_u03b2_310_, lean_object* v_x_311_, lean_object* v_x_312_, lean_object* v_x_313_, lean_object* v_x_314_){
_start:
{
size_t v_x_2455__boxed_315_; lean_object* v_res_316_; 
v_x_2455__boxed_315_ = lean_unbox_usize(v_x_312_);
lean_dec(v_x_312_);
v_res_316_ = l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0(v_00_u03b2_310_, v_x_311_, v_x_2455__boxed_315_, v_x_313_, v_x_314_);
lean_dec_ref(v_x_314_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1(lean_object* v_00_u03b2_317_, lean_object* v_x_318_, lean_object* v_x_319_, lean_object* v_x_320_){
_start:
{
lean_object* v___x_321_; 
v___x_321_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1___redArg(v_x_318_, v_x_319_, v_x_320_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0(lean_object* v_00_u03b2_322_, lean_object* v_keys_323_, lean_object* v_vals_324_, lean_object* v_heq_325_, lean_object* v_i_326_, lean_object* v_k_327_, lean_object* v_k_u2080_328_){
_start:
{
lean_object* v___x_329_; 
v___x_329_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0___redArg(v_keys_323_, v_i_326_, v_k_327_, v_k_u2080_328_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0___boxed(lean_object* v_00_u03b2_330_, lean_object* v_keys_331_, lean_object* v_vals_332_, lean_object* v_heq_333_, lean_object* v_i_334_, lean_object* v_k_335_, lean_object* v_k_u2080_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0(v_00_u03b2_330_, v_keys_331_, v_vals_332_, v_heq_333_, v_i_334_, v_k_335_, v_k_u2080_336_);
lean_dec_ref(v_k_u2080_336_);
lean_dec_ref(v_vals_332_);
lean_dec_ref(v_keys_331_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2(lean_object* v_00_u03b2_338_, lean_object* v_x_339_, size_t v_x_340_, size_t v_x_341_, lean_object* v_x_342_, lean_object* v_x_343_){
_start:
{
lean_object* v___x_344_; 
v___x_344_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg(v_x_339_, v_x_340_, v_x_341_, v_x_342_, v_x_343_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_345_, lean_object* v_x_346_, lean_object* v_x_347_, lean_object* v_x_348_, lean_object* v_x_349_, lean_object* v_x_350_){
_start:
{
size_t v_x_2479__boxed_351_; size_t v_x_2480__boxed_352_; lean_object* v_res_353_; 
v_x_2479__boxed_351_ = lean_unbox_usize(v_x_347_);
lean_dec(v_x_347_);
v_x_2480__boxed_352_ = lean_unbox_usize(v_x_348_);
lean_dec(v_x_348_);
v_res_353_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2(v_00_u03b2_345_, v_x_346_, v_x_2479__boxed_351_, v_x_2480__boxed_352_, v_x_349_, v_x_350_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_354_, lean_object* v_n_355_, lean_object* v_k_356_, lean_object* v_v_357_){
_start:
{
lean_object* v___x_358_; 
v___x_358_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__3___redArg(v_n_355_, v_k_356_, v_v_357_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_359_, size_t v_depth_360_, lean_object* v_keys_361_, lean_object* v_vals_362_, lean_object* v_heq_363_, lean_object* v_i_364_, lean_object* v_entries_365_){
_start:
{
lean_object* v___x_366_; 
v___x_366_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4___redArg(v_depth_360_, v_keys_361_, v_vals_362_, v_i_364_, v_entries_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_367_, lean_object* v_depth_368_, lean_object* v_keys_369_, lean_object* v_vals_370_, lean_object* v_heq_371_, lean_object* v_i_372_, lean_object* v_entries_373_){
_start:
{
size_t v_depth_boxed_374_; lean_object* v_res_375_; 
v_depth_boxed_374_ = lean_unbox_usize(v_depth_368_);
lean_dec(v_depth_368_);
v_res_375_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4(v_00_u03b2_367_, v_depth_boxed_374_, v_keys_369_, v_vals_370_, v_heq_371_, v_i_372_, v_entries_373_);
lean_dec_ref(v_vals_370_);
lean_dec_ref(v_keys_369_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_376_, lean_object* v_x_377_, lean_object* v_x_378_, lean_object* v_x_379_, lean_object* v_x_380_){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__3_spec__4___redArg(v_x_377_, v_x_378_, v_x_379_, v_x_380_);
return v___x_381_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0(void){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = l_Lean_Meta_Sym_instInhabitedSymM(lean_box(0));
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0(lean_object* v_msg_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
lean_object* v___x_391_; lean_object* v___x_756__overap_392_; lean_object* v___x_393_; 
v___x_391_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0, &l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0);
v___x_756__overap_392_ = lean_panic_fn_borrowed(v___x_391_, v_msg_383_);
lean_inc(v___y_389_);
lean_inc_ref(v___y_388_);
lean_inc(v___y_387_);
lean_inc_ref(v___y_386_);
lean_inc(v___y_385_);
lean_inc_ref(v___y_384_);
v___x_393_ = lean_apply_7(v___x_756__overap_392_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, lean_box(0));
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___boxed(lean_object* v_msg_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0(v_msg_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_);
lean_dec(v___y_400_);
lean_dec_ref(v___y_399_);
lean_dec(v___y_398_);
lean_dec_ref(v___y_397_);
lean_dec(v___y_396_);
lean_dec_ref(v___y_395_);
return v_res_402_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__3(void){
_start:
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_406_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__2));
v___x_407_ = lean_unsigned_to_nat(2u);
v___x_408_ = lean_unsigned_to_nat(42u);
v___x_409_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__1));
v___x_410_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_411_ = l_mkPanicMessageWithDecl(v___x_410_, v___x_409_, v___x_408_, v___x_407_, v___x_406_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object* v_e_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_){
_start:
{
lean_object* v___x_420_; lean_object* v_share_421_; lean_object* v___x_422_; uint64_t v___x_423_; size_t v___x_424_; lean_object* v___x_425_; uint8_t v___x_426_; 
v___x_420_ = lean_st_ref_get(v_a_414_);
v_share_421_ = lean_ctor_get(v___x_420_, 0);
lean_inc_ref(v_share_421_);
lean_dec(v___x_420_);
v___x_422_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy;
v___x_423_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_412_);
v___x_424_ = lean_uint64_to_usize(v___x_423_);
lean_inc_ref(v_e_412_);
v___x_425_ = l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg(v_share_421_, v___x_424_, v_e_412_, v___x_422_);
v___x_426_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_425_, v_e_412_);
lean_dec_ref(v_e_412_);
lean_dec_ref(v___x_425_);
if (v___x_426_ == 0)
{
lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_427_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__3, &l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__3_once, _init_l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__3);
v___x_428_ = l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0(v___x_427_, v_a_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_, v_a_418_);
return v___x_428_;
}
else
{
lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_429_ = lean_box(0);
v___x_430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_430_, 0, v___x_429_);
return v___x_430_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared___boxed(lean_object* v_e_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_e_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_);
lean_dec(v_a_437_);
lean_dec_ref(v_a_436_);
lean_dec(v_a_435_);
lean_dec_ref(v_a_434_);
lean_dec(v_a_433_);
lean_dec_ref(v_a_432_);
return v_res_439_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2(void){
_start:
{
lean_object* v___f_450_; lean_object* v___f_451_; lean_object* v___x_452_; 
v___f_450_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__1));
v___f_451_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__0));
v___x_452_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___f_451_, v___f_450_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM___redArg(lean_object* v_k_453_, lean_object* v_a_454_){
_start:
{
lean_object* v___x_456_; lean_object* v_share_457_; lean_object* v_maxFVar_458_; lean_object* v_proofInstInfo_459_; lean_object* v_inferType_460_; lean_object* v_getLevel_461_; lean_object* v_congrInfo_462_; lean_object* v_defEqI_463_; lean_object* v_extensions_464_; lean_object* v_issues_465_; lean_object* v_canon_466_; uint8_t v_debug_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_503_; 
v___x_456_ = lean_st_ref_take(v_a_454_);
v_share_457_ = lean_ctor_get(v___x_456_, 0);
v_maxFVar_458_ = lean_ctor_get(v___x_456_, 1);
v_proofInstInfo_459_ = lean_ctor_get(v___x_456_, 2);
v_inferType_460_ = lean_ctor_get(v___x_456_, 3);
v_getLevel_461_ = lean_ctor_get(v___x_456_, 4);
v_congrInfo_462_ = lean_ctor_get(v___x_456_, 5);
v_defEqI_463_ = lean_ctor_get(v___x_456_, 6);
v_extensions_464_ = lean_ctor_get(v___x_456_, 7);
v_issues_465_ = lean_ctor_get(v___x_456_, 8);
v_canon_466_ = lean_ctor_get(v___x_456_, 9);
v_debug_467_ = lean_ctor_get_uint8(v___x_456_, sizeof(void*)*10);
v_isSharedCheck_503_ = !lean_is_exclusive(v___x_456_);
if (v_isSharedCheck_503_ == 0)
{
v___x_469_ = v___x_456_;
v_isShared_470_ = v_isSharedCheck_503_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_canon_466_);
lean_inc(v_issues_465_);
lean_inc(v_extensions_464_);
lean_inc(v_defEqI_463_);
lean_inc(v_congrInfo_462_);
lean_inc(v_getLevel_461_);
lean_inc(v_inferType_460_);
lean_inc(v_proofInstInfo_459_);
lean_inc(v_maxFVar_458_);
lean_inc(v_share_457_);
lean_dec(v___x_456_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_503_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
lean_object* v___x_471_; lean_object* v___x_473_; 
v___x_471_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2, &l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2_once, _init_l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2);
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 0, v___x_471_);
v___x_473_ = v___x_469_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v___x_471_);
lean_ctor_set(v_reuseFailAlloc_502_, 1, v_maxFVar_458_);
lean_ctor_set(v_reuseFailAlloc_502_, 2, v_proofInstInfo_459_);
lean_ctor_set(v_reuseFailAlloc_502_, 3, v_inferType_460_);
lean_ctor_set(v_reuseFailAlloc_502_, 4, v_getLevel_461_);
lean_ctor_set(v_reuseFailAlloc_502_, 5, v_congrInfo_462_);
lean_ctor_set(v_reuseFailAlloc_502_, 6, v_defEqI_463_);
lean_ctor_set(v_reuseFailAlloc_502_, 7, v_extensions_464_);
lean_ctor_set(v_reuseFailAlloc_502_, 8, v_issues_465_);
lean_ctor_set(v_reuseFailAlloc_502_, 9, v_canon_466_);
lean_ctor_set_uint8(v_reuseFailAlloc_502_, sizeof(void*)*10, v_debug_467_);
v___x_473_ = v_reuseFailAlloc_502_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
lean_object* v___x_474_; lean_object* v___x_475_; uint8_t v_debug_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v_fst_479_; lean_object* v_snd_480_; lean_object* v___x_481_; lean_object* v_maxFVar_482_; lean_object* v_proofInstInfo_483_; lean_object* v_inferType_484_; lean_object* v_getLevel_485_; lean_object* v_congrInfo_486_; lean_object* v_defEqI_487_; lean_object* v_extensions_488_; lean_object* v_issues_489_; lean_object* v_canon_490_; uint8_t v_debug_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_500_; 
v___x_474_ = lean_st_ref_set(v_a_454_, v___x_473_);
v___x_475_ = lean_st_ref_get(v_a_454_);
v_debug_476_ = lean_ctor_get_uint8(v___x_475_, sizeof(void*)*10);
lean_dec(v___x_475_);
v___x_477_ = lean_box(v_debug_476_);
v___x_478_ = lean_apply_2(v_k_453_, v___x_477_, v_share_457_);
v_fst_479_ = lean_ctor_get(v___x_478_, 0);
lean_inc(v_fst_479_);
v_snd_480_ = lean_ctor_get(v___x_478_, 1);
lean_inc(v_snd_480_);
lean_dec_ref(v___x_478_);
v___x_481_ = lean_st_ref_take(v_a_454_);
v_maxFVar_482_ = lean_ctor_get(v___x_481_, 1);
v_proofInstInfo_483_ = lean_ctor_get(v___x_481_, 2);
v_inferType_484_ = lean_ctor_get(v___x_481_, 3);
v_getLevel_485_ = lean_ctor_get(v___x_481_, 4);
v_congrInfo_486_ = lean_ctor_get(v___x_481_, 5);
v_defEqI_487_ = lean_ctor_get(v___x_481_, 6);
v_extensions_488_ = lean_ctor_get(v___x_481_, 7);
v_issues_489_ = lean_ctor_get(v___x_481_, 8);
v_canon_490_ = lean_ctor_get(v___x_481_, 9);
v_debug_491_ = lean_ctor_get_uint8(v___x_481_, sizeof(void*)*10);
v_isSharedCheck_500_ = !lean_is_exclusive(v___x_481_);
if (v_isSharedCheck_500_ == 0)
{
lean_object* v_unused_501_; 
v_unused_501_ = lean_ctor_get(v___x_481_, 0);
lean_dec(v_unused_501_);
v___x_493_ = v___x_481_;
v_isShared_494_ = v_isSharedCheck_500_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_canon_490_);
lean_inc(v_issues_489_);
lean_inc(v_extensions_488_);
lean_inc(v_defEqI_487_);
lean_inc(v_congrInfo_486_);
lean_inc(v_getLevel_485_);
lean_inc(v_inferType_484_);
lean_inc(v_proofInstInfo_483_);
lean_inc(v_maxFVar_482_);
lean_dec(v___x_481_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_500_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_496_; 
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 0, v_snd_480_);
v___x_496_ = v___x_493_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v_snd_480_);
lean_ctor_set(v_reuseFailAlloc_499_, 1, v_maxFVar_482_);
lean_ctor_set(v_reuseFailAlloc_499_, 2, v_proofInstInfo_483_);
lean_ctor_set(v_reuseFailAlloc_499_, 3, v_inferType_484_);
lean_ctor_set(v_reuseFailAlloc_499_, 4, v_getLevel_485_);
lean_ctor_set(v_reuseFailAlloc_499_, 5, v_congrInfo_486_);
lean_ctor_set(v_reuseFailAlloc_499_, 6, v_defEqI_487_);
lean_ctor_set(v_reuseFailAlloc_499_, 7, v_extensions_488_);
lean_ctor_set(v_reuseFailAlloc_499_, 8, v_issues_489_);
lean_ctor_set(v_reuseFailAlloc_499_, 9, v_canon_490_);
lean_ctor_set_uint8(v_reuseFailAlloc_499_, sizeof(void*)*10, v_debug_491_);
v___x_496_ = v_reuseFailAlloc_499_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_497_ = lean_st_ref_set(v_a_454_, v___x_496_);
v___x_498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_498_, 0, v_fst_479_);
return v___x_498_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___boxed(lean_object* v_k_504_, lean_object* v_a_505_, lean_object* v_a_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l_Lean_Meta_Sym_Internal_liftBuilderM___redArg(v_k_504_, v_a_505_);
lean_dec(v_a_505_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM(lean_object* v_00_u03b1_508_, lean_object* v_k_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_){
_start:
{
lean_object* v___x_517_; lean_object* v_share_518_; lean_object* v_maxFVar_519_; lean_object* v_proofInstInfo_520_; lean_object* v_inferType_521_; lean_object* v_getLevel_522_; lean_object* v_congrInfo_523_; lean_object* v_defEqI_524_; lean_object* v_extensions_525_; lean_object* v_issues_526_; lean_object* v_canon_527_; uint8_t v_debug_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_564_; 
v___x_517_ = lean_st_ref_take(v_a_511_);
v_share_518_ = lean_ctor_get(v___x_517_, 0);
v_maxFVar_519_ = lean_ctor_get(v___x_517_, 1);
v_proofInstInfo_520_ = lean_ctor_get(v___x_517_, 2);
v_inferType_521_ = lean_ctor_get(v___x_517_, 3);
v_getLevel_522_ = lean_ctor_get(v___x_517_, 4);
v_congrInfo_523_ = lean_ctor_get(v___x_517_, 5);
v_defEqI_524_ = lean_ctor_get(v___x_517_, 6);
v_extensions_525_ = lean_ctor_get(v___x_517_, 7);
v_issues_526_ = lean_ctor_get(v___x_517_, 8);
v_canon_527_ = lean_ctor_get(v___x_517_, 9);
v_debug_528_ = lean_ctor_get_uint8(v___x_517_, sizeof(void*)*10);
v_isSharedCheck_564_ = !lean_is_exclusive(v___x_517_);
if (v_isSharedCheck_564_ == 0)
{
v___x_530_ = v___x_517_;
v_isShared_531_ = v_isSharedCheck_564_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_canon_527_);
lean_inc(v_issues_526_);
lean_inc(v_extensions_525_);
lean_inc(v_defEqI_524_);
lean_inc(v_congrInfo_523_);
lean_inc(v_getLevel_522_);
lean_inc(v_inferType_521_);
lean_inc(v_proofInstInfo_520_);
lean_inc(v_maxFVar_519_);
lean_inc(v_share_518_);
lean_dec(v___x_517_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_564_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_532_; lean_object* v___x_534_; 
v___x_532_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2, &l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2_once, _init_l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2);
if (v_isShared_531_ == 0)
{
lean_ctor_set(v___x_530_, 0, v___x_532_);
v___x_534_ = v___x_530_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v___x_532_);
lean_ctor_set(v_reuseFailAlloc_563_, 1, v_maxFVar_519_);
lean_ctor_set(v_reuseFailAlloc_563_, 2, v_proofInstInfo_520_);
lean_ctor_set(v_reuseFailAlloc_563_, 3, v_inferType_521_);
lean_ctor_set(v_reuseFailAlloc_563_, 4, v_getLevel_522_);
lean_ctor_set(v_reuseFailAlloc_563_, 5, v_congrInfo_523_);
lean_ctor_set(v_reuseFailAlloc_563_, 6, v_defEqI_524_);
lean_ctor_set(v_reuseFailAlloc_563_, 7, v_extensions_525_);
lean_ctor_set(v_reuseFailAlloc_563_, 8, v_issues_526_);
lean_ctor_set(v_reuseFailAlloc_563_, 9, v_canon_527_);
lean_ctor_set_uint8(v_reuseFailAlloc_563_, sizeof(void*)*10, v_debug_528_);
v___x_534_ = v_reuseFailAlloc_563_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
lean_object* v___x_535_; lean_object* v___x_536_; uint8_t v_debug_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v_fst_540_; lean_object* v_snd_541_; lean_object* v___x_542_; lean_object* v_maxFVar_543_; lean_object* v_proofInstInfo_544_; lean_object* v_inferType_545_; lean_object* v_getLevel_546_; lean_object* v_congrInfo_547_; lean_object* v_defEqI_548_; lean_object* v_extensions_549_; lean_object* v_issues_550_; lean_object* v_canon_551_; uint8_t v_debug_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_561_; 
v___x_535_ = lean_st_ref_set(v_a_511_, v___x_534_);
v___x_536_ = lean_st_ref_get(v_a_511_);
v_debug_537_ = lean_ctor_get_uint8(v___x_536_, sizeof(void*)*10);
lean_dec(v___x_536_);
v___x_538_ = lean_box(v_debug_537_);
v___x_539_ = lean_apply_2(v_k_509_, v___x_538_, v_share_518_);
v_fst_540_ = lean_ctor_get(v___x_539_, 0);
lean_inc(v_fst_540_);
v_snd_541_ = lean_ctor_get(v___x_539_, 1);
lean_inc(v_snd_541_);
lean_dec_ref(v___x_539_);
v___x_542_ = lean_st_ref_take(v_a_511_);
v_maxFVar_543_ = lean_ctor_get(v___x_542_, 1);
v_proofInstInfo_544_ = lean_ctor_get(v___x_542_, 2);
v_inferType_545_ = lean_ctor_get(v___x_542_, 3);
v_getLevel_546_ = lean_ctor_get(v___x_542_, 4);
v_congrInfo_547_ = lean_ctor_get(v___x_542_, 5);
v_defEqI_548_ = lean_ctor_get(v___x_542_, 6);
v_extensions_549_ = lean_ctor_get(v___x_542_, 7);
v_issues_550_ = lean_ctor_get(v___x_542_, 8);
v_canon_551_ = lean_ctor_get(v___x_542_, 9);
v_debug_552_ = lean_ctor_get_uint8(v___x_542_, sizeof(void*)*10);
v_isSharedCheck_561_ = !lean_is_exclusive(v___x_542_);
if (v_isSharedCheck_561_ == 0)
{
lean_object* v_unused_562_; 
v_unused_562_ = lean_ctor_get(v___x_542_, 0);
lean_dec(v_unused_562_);
v___x_554_ = v___x_542_;
v_isShared_555_ = v_isSharedCheck_561_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_canon_551_);
lean_inc(v_issues_550_);
lean_inc(v_extensions_549_);
lean_inc(v_defEqI_548_);
lean_inc(v_congrInfo_547_);
lean_inc(v_getLevel_546_);
lean_inc(v_inferType_545_);
lean_inc(v_proofInstInfo_544_);
lean_inc(v_maxFVar_543_);
lean_dec(v___x_542_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_561_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v___x_557_; 
if (v_isShared_555_ == 0)
{
lean_ctor_set(v___x_554_, 0, v_snd_541_);
v___x_557_ = v___x_554_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v_snd_541_);
lean_ctor_set(v_reuseFailAlloc_560_, 1, v_maxFVar_543_);
lean_ctor_set(v_reuseFailAlloc_560_, 2, v_proofInstInfo_544_);
lean_ctor_set(v_reuseFailAlloc_560_, 3, v_inferType_545_);
lean_ctor_set(v_reuseFailAlloc_560_, 4, v_getLevel_546_);
lean_ctor_set(v_reuseFailAlloc_560_, 5, v_congrInfo_547_);
lean_ctor_set(v_reuseFailAlloc_560_, 6, v_defEqI_548_);
lean_ctor_set(v_reuseFailAlloc_560_, 7, v_extensions_549_);
lean_ctor_set(v_reuseFailAlloc_560_, 8, v_issues_550_);
lean_ctor_set(v_reuseFailAlloc_560_, 9, v_canon_551_);
lean_ctor_set_uint8(v_reuseFailAlloc_560_, sizeof(void*)*10, v_debug_552_);
v___x_557_ = v_reuseFailAlloc_560_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_558_ = lean_st_ref_set(v_a_511_, v___x_557_);
v___x_559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_559_, 0, v_fst_540_);
return v___x_559_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM___boxed(lean_object* v_00_u03b1_565_, lean_object* v_k_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l_Lean_Meta_Sym_Internal_liftBuilderM(v_00_u03b1_565_, v_k_566_, v_a_567_, v_a_568_, v_a_569_, v_a_570_, v_a_571_, v_a_572_);
lean_dec(v_a_572_);
lean_dec_ref(v_a_571_);
lean_dec(v_a_570_);
lean_dec_ref(v_a_569_);
lean_dec(v_a_568_);
lean_dec_ref(v_a_567_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_share1___redArg(lean_object* v_e_575_, lean_object* v_a_576_){
_start:
{
lean_object* v___x_577_; uint64_t v___x_578_; size_t v___x_579_; lean_object* v___x_580_; uint8_t v___x_581_; 
v___x_577_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy;
v___x_578_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_575_);
v___x_579_ = lean_uint64_to_usize(v___x_578_);
lean_inc_ref(v_e_575_);
lean_inc_ref(v_a_576_);
v___x_580_ = l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg(v_a_576_, v___x_579_, v_e_575_, v___x_577_);
v___x_581_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_580_, v___x_577_);
if (v___x_581_ == 0)
{
lean_object* v___x_582_; 
lean_dec_ref(v_e_575_);
v___x_582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_582_, 0, v___x_580_);
lean_ctor_set(v___x_582_, 1, v_a_576_);
return v___x_582_;
}
else
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
lean_dec_ref(v___x_580_);
v___x_583_ = lean_box(0);
lean_inc_ref(v_e_575_);
v___x_584_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1___redArg(v_a_576_, v_e_575_, v___x_583_);
v___x_585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_585_, 0, v_e_575_);
lean_ctor_set(v___x_585_, 1, v___x_584_);
return v___x_585_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_share1(lean_object* v_e_586_, uint8_t v_a_587_, lean_object* v_a_588_){
_start:
{
lean_object* v___x_589_; 
v___x_589_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v_e_586_, v_a_588_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_share1___boxed(lean_object* v_e_590_, lean_object* v_a_591_, lean_object* v_a_592_){
_start:
{
uint8_t v_a_boxed_593_; lean_object* v_res_594_; 
v_a_boxed_593_ = lean_unbox(v_a_591_);
v_res_594_ = l_Lean_Meta_Sym_Internal_Builder_share1(v_e_590_, v_a_boxed_593_, v_a_592_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1(lean_object* v_msg_602_, uint8_t v___y_603_, lean_object* v___y_604_){
_start:
{
lean_object* v___f_605_; lean_object* v___f_606_; lean_object* v___f_607_; lean_object* v___f_608_; lean_object* v___f_609_; lean_object* v___f_610_; lean_object* v___f_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___f_615_; lean_object* v___f_616_; lean_object* v___f_617_; lean_object* v___f_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___f_627_; lean_object* v___x_692__overap_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v___f_605_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__0));
v___f_606_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__1));
v___f_607_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__2));
v___f_608_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__3));
v___f_609_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__4));
v___f_610_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__5));
v___f_611_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__6));
v___x_612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_612_, 0, v___f_605_);
lean_ctor_set(v___x_612_, 1, v___f_606_);
v___x_613_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_613_, 0, v___x_612_);
lean_ctor_set(v___x_613_, 1, v___f_607_);
lean_ctor_set(v___x_613_, 2, v___f_608_);
lean_ctor_set(v___x_613_, 3, v___f_609_);
lean_ctor_set(v___x_613_, 4, v___f_610_);
v___x_614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_614_, 0, v___x_613_);
lean_ctor_set(v___x_614_, 1, v___f_611_);
lean_inc_ref_n(v___x_614_, 6);
v___f_615_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_615_, 0, v___x_614_);
v___f_616_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_616_, 0, v___x_614_);
v___f_617_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_617_, 0, v___x_614_);
v___f_618_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_618_, 0, v___x_614_);
v___x_619_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_619_, 0, lean_box(0));
lean_closure_set(v___x_619_, 1, lean_box(0));
lean_closure_set(v___x_619_, 2, v___x_614_);
v___x_620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_620_, 0, v___x_619_);
lean_ctor_set(v___x_620_, 1, v___f_615_);
v___x_621_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_621_, 0, lean_box(0));
lean_closure_set(v___x_621_, 1, lean_box(0));
lean_closure_set(v___x_621_, 2, v___x_614_);
v___x_622_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_622_, 0, v___x_620_);
lean_ctor_set(v___x_622_, 1, v___x_621_);
lean_ctor_set(v___x_622_, 2, v___f_616_);
lean_ctor_set(v___x_622_, 3, v___f_617_);
lean_ctor_set(v___x_622_, 4, v___f_618_);
v___x_623_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_623_, 0, lean_box(0));
lean_closure_set(v___x_623_, 1, lean_box(0));
lean_closure_set(v___x_623_, 2, v___x_614_);
v___x_624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_624_, 0, v___x_622_);
lean_ctor_set(v___x_624_, 1, v___x_623_);
v___x_625_ = lean_box(0);
v___x_626_ = l_instInhabitedOfMonad___redArg(v___x_624_, v___x_625_);
v___f_627_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_627_, 0, v___x_626_);
v___x_692__overap_628_ = lean_panic_fn_borrowed(v___f_627_, v_msg_602_);
lean_dec_ref(v___f_627_);
v___x_629_ = lean_box(v___y_603_);
v___x_630_ = lean_apply_2(v___x_692__overap_628_, v___x_629_, v___y_604_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___boxed(lean_object* v_msg_631_, lean_object* v___y_632_, lean_object* v___y_633_){
_start:
{
uint8_t v___y_825__boxed_634_; lean_object* v_res_635_; 
v___y_825__boxed_634_ = lean_unbox(v___y_632_);
v_res_635_ = l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1(v_msg_631_, v___y_825__boxed_634_, v___y_633_);
return v_res_635_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_636_, lean_object* v_i_637_, lean_object* v_k_638_){
_start:
{
lean_object* v___x_639_; uint8_t v___x_640_; 
v___x_639_ = lean_array_get_size(v_keys_636_);
v___x_640_ = lean_nat_dec_lt(v_i_637_, v___x_639_);
if (v___x_640_ == 0)
{
lean_dec_ref(v_k_638_);
lean_dec(v_i_637_);
return v___x_640_;
}
else
{
lean_object* v_k_x27_641_; uint8_t v___x_642_; 
v_k_x27_641_ = lean_array_fget_borrowed(v_keys_636_, v_i_637_);
lean_inc(v_k_x27_641_);
lean_inc_ref(v_k_638_);
v___x_642_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_k_638_, v_k_x27_641_);
if (v___x_642_ == 0)
{
lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_643_ = lean_unsigned_to_nat(1u);
v___x_644_ = lean_nat_add(v_i_637_, v___x_643_);
lean_dec(v_i_637_);
v_i_637_ = v___x_644_;
goto _start;
}
else
{
lean_dec_ref(v_k_638_);
lean_dec(v_i_637_);
return v___x_642_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_646_, lean_object* v_i_647_, lean_object* v_k_648_){
_start:
{
uint8_t v_res_649_; lean_object* v_r_650_; 
v_res_649_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg(v_keys_646_, v_i_647_, v_k_648_);
lean_dec_ref(v_keys_646_);
v_r_650_ = lean_box(v_res_649_);
return v_r_650_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg(lean_object* v_x_651_, size_t v_x_652_, lean_object* v_x_653_){
_start:
{
if (lean_obj_tag(v_x_651_) == 0)
{
lean_object* v_es_654_; lean_object* v___x_655_; size_t v___x_656_; size_t v___x_657_; size_t v___x_658_; lean_object* v_j_659_; lean_object* v___x_660_; 
v_es_654_ = lean_ctor_get(v_x_651_, 0);
lean_inc_ref(v_es_654_);
lean_dec_ref(v_x_651_);
v___x_655_ = lean_box(2);
v___x_656_ = ((size_t)5ULL);
v___x_657_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__1);
v___x_658_ = lean_usize_land(v_x_652_, v___x_657_);
v_j_659_ = lean_usize_to_nat(v___x_658_);
v___x_660_ = lean_array_get(v___x_655_, v_es_654_, v_j_659_);
lean_dec(v_j_659_);
lean_dec_ref(v_es_654_);
switch(lean_obj_tag(v___x_660_))
{
case 0:
{
lean_object* v_key_661_; uint8_t v___x_662_; 
v_key_661_ = lean_ctor_get(v___x_660_, 0);
lean_inc(v_key_661_);
lean_dec_ref(v___x_660_);
v___x_662_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_653_, v_key_661_);
return v___x_662_;
}
case 1:
{
lean_object* v_node_663_; size_t v___x_664_; 
v_node_663_ = lean_ctor_get(v___x_660_, 0);
lean_inc(v_node_663_);
lean_dec_ref(v___x_660_);
v___x_664_ = lean_usize_shift_right(v_x_652_, v___x_656_);
v_x_651_ = v_node_663_;
v_x_652_ = v___x_664_;
goto _start;
}
default: 
{
uint8_t v___x_666_; 
lean_dec_ref(v_x_653_);
v___x_666_ = 0;
return v___x_666_;
}
}
}
else
{
lean_object* v_ks_667_; lean_object* v___x_668_; uint8_t v___x_669_; 
v_ks_667_ = lean_ctor_get(v_x_651_, 0);
lean_inc_ref(v_ks_667_);
lean_dec_ref(v_x_651_);
v___x_668_ = lean_unsigned_to_nat(0u);
v___x_669_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg(v_ks_667_, v___x_668_, v_x_653_);
lean_dec_ref(v_ks_667_);
return v___x_669_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg___boxed(lean_object* v_x_670_, lean_object* v_x_671_, lean_object* v_x_672_){
_start:
{
size_t v_x_907__boxed_673_; uint8_t v_res_674_; lean_object* v_r_675_; 
v_x_907__boxed_673_ = lean_unbox_usize(v_x_671_);
lean_dec(v_x_671_);
v_res_674_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg(v_x_670_, v_x_907__boxed_673_, v_x_672_);
v_r_675_ = lean_box(v_res_674_);
return v_r_675_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg(lean_object* v_x_676_, lean_object* v_x_677_){
_start:
{
uint64_t v___x_678_; size_t v___x_679_; uint8_t v___x_680_; 
v___x_678_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_677_);
v___x_679_ = lean_uint64_to_usize(v___x_678_);
v___x_680_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg(v_x_676_, v___x_679_, v_x_677_);
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg___boxed(lean_object* v_x_681_, lean_object* v_x_682_){
_start:
{
uint8_t v_res_683_; lean_object* v_r_684_; 
v_res_683_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg(v_x_681_, v_x_682_);
v_r_684_ = lean_box(v_res_683_);
return v_r_684_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__2(void){
_start:
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_687_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__1));
v___x_688_ = lean_unsigned_to_nat(2u);
v___x_689_ = lean_unsigned_to_nat(74u);
v___x_690_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__0));
v___x_691_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_692_ = l_mkPanicMessageWithDecl(v___x_691_, v___x_690_, v___x_689_, v___x_688_, v___x_687_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_assertShared(lean_object* v_e_693_, uint8_t v_a_694_, lean_object* v_a_695_){
_start:
{
uint8_t v___x_696_; 
lean_inc_ref(v_a_695_);
v___x_696_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg(v_a_695_, v_e_693_);
if (v___x_696_ == 0)
{
lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_697_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__2, &l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__2_once, _init_l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__2);
v___x_698_ = l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1(v___x_697_, v_a_694_, v_a_695_);
return v___x_698_;
}
else
{
lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_699_ = lean_box(0);
v___x_700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_700_, 0, v___x_699_);
lean_ctor_set(v___x_700_, 1, v_a_695_);
return v___x_700_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_assertShared___boxed(lean_object* v_e_701_, lean_object* v_a_702_, lean_object* v_a_703_){
_start:
{
uint8_t v_a_boxed_704_; lean_object* v_res_705_; 
v_a_boxed_704_ = lean_unbox(v_a_702_);
v_res_705_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_e_701_, v_a_boxed_704_, v_a_703_);
return v_res_705_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0(lean_object* v_00_u03b2_706_, lean_object* v_x_707_, lean_object* v_x_708_){
_start:
{
uint8_t v___x_709_; 
v___x_709_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg(v_x_707_, v_x_708_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___boxed(lean_object* v_00_u03b2_710_, lean_object* v_x_711_, lean_object* v_x_712_){
_start:
{
uint8_t v_res_713_; lean_object* v_r_714_; 
v_res_713_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0(v_00_u03b2_710_, v_x_711_, v_x_712_);
v_r_714_ = lean_box(v_res_713_);
return v_r_714_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0(lean_object* v_00_u03b2_715_, lean_object* v_x_716_, size_t v_x_717_, lean_object* v_x_718_){
_start:
{
uint8_t v___x_719_; 
v___x_719_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg(v_x_716_, v_x_717_, v_x_718_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___boxed(lean_object* v_00_u03b2_720_, lean_object* v_x_721_, lean_object* v_x_722_, lean_object* v_x_723_){
_start:
{
size_t v_x_1008__boxed_724_; uint8_t v_res_725_; lean_object* v_r_726_; 
v_x_1008__boxed_724_ = lean_unbox_usize(v_x_722_);
lean_dec(v_x_722_);
v_res_725_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0(v_00_u03b2_720_, v_x_721_, v_x_1008__boxed_724_, v_x_723_);
v_r_726_ = lean_box(v_res_725_);
return v_r_726_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_727_, lean_object* v_keys_728_, lean_object* v_vals_729_, lean_object* v_heq_730_, lean_object* v_i_731_, lean_object* v_k_732_){
_start:
{
uint8_t v___x_733_; 
v___x_733_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg(v_keys_728_, v_i_731_, v_k_732_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_734_, lean_object* v_keys_735_, lean_object* v_vals_736_, lean_object* v_heq_737_, lean_object* v_i_738_, lean_object* v_k_739_){
_start:
{
uint8_t v_res_740_; lean_object* v_r_741_; 
v_res_740_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2(v_00_u03b2_734_, v_keys_735_, v_vals_736_, v_heq_737_, v_i_738_, v_k_739_);
lean_dec_ref(v_vals_736_);
lean_dec_ref(v_keys_735_);
v_r_741_ = lean_box(v_res_740_);
return v_r_741_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM(void){
_start:
{
lean_object* v___f_744_; lean_object* v___f_745_; lean_object* v___f_746_; lean_object* v___f_747_; lean_object* v___f_748_; lean_object* v___f_749_; lean_object* v___f_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___f_754_; lean_object* v___f_755_; lean_object* v___f_756_; lean_object* v___f_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
v___f_744_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__0));
v___f_745_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__1));
v___f_746_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__2));
v___f_747_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__3));
v___f_748_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__4));
v___f_749_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__5));
v___f_750_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__6));
v___x_751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_751_, 0, v___f_744_);
lean_ctor_set(v___x_751_, 1, v___f_745_);
v___x_752_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_752_, 0, v___x_751_);
lean_ctor_set(v___x_752_, 1, v___f_746_);
lean_ctor_set(v___x_752_, 2, v___f_747_);
lean_ctor_set(v___x_752_, 3, v___f_748_);
lean_ctor_set(v___x_752_, 4, v___f_749_);
v___x_753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_753_, 0, v___x_752_);
lean_ctor_set(v___x_753_, 1, v___f_750_);
lean_inc_ref_n(v___x_753_, 6);
v___f_754_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_754_, 0, v___x_753_);
v___f_755_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_755_, 0, v___x_753_);
v___f_756_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_756_, 0, v___x_753_);
v___f_757_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_757_, 0, v___x_753_);
v___x_758_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_758_, 0, lean_box(0));
lean_closure_set(v___x_758_, 1, lean_box(0));
lean_closure_set(v___x_758_, 2, v___x_753_);
v___x_759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_759_, 0, v___x_758_);
lean_ctor_set(v___x_759_, 1, v___f_754_);
v___x_760_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_760_, 0, lean_box(0));
lean_closure_set(v___x_760_, 1, lean_box(0));
lean_closure_set(v___x_760_, 2, v___x_753_);
v___x_761_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_761_, 0, v___x_759_);
lean_ctor_set(v___x_761_, 1, v___x_760_);
lean_ctor_set(v___x_761_, 2, v___f_755_);
lean_ctor_set(v___x_761_, 3, v___f_756_);
lean_ctor_set(v___x_761_, 4, v___f_757_);
v___x_762_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_762_, 0, lean_box(0));
lean_closure_set(v___x_762_, 1, lean_box(0));
lean_closure_set(v___x_762_, 2, v___x_753_);
v___x_763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_763_, 0, v___x_761_);
lean_ctor_set(v___x_763_, 1, v___x_762_);
v___x_764_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__0));
v___x_765_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__1));
v___x_766_ = lean_alloc_closure((void*)(l_ReaderT_read___boxed), 4, 3);
lean_closure_set(v___x_766_, 0, lean_box(0));
lean_closure_set(v___x_766_, 1, lean_box(0));
lean_closure_set(v___x_766_, 2, v___x_763_);
v___x_767_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_767_, 0, v___x_764_);
lean_ctor_set(v___x_767_, 1, v___x_765_);
lean_ctor_set(v___x_767_, 2, v___x_766_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLitS___redArg(lean_object* v_inst_768_, lean_object* v_l_769_){
_start:
{
lean_object* v_share1_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
v_share1_770_ = lean_ctor_get(v_inst_768_, 0);
lean_inc(v_share1_770_);
lean_dec_ref(v_inst_768_);
v___x_771_ = l_Lean_Expr_lit___override(v_l_769_);
v___x_772_ = lean_apply_1(v_share1_770_, v___x_771_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLitS(lean_object* v_m_773_, lean_object* v_inst_774_, lean_object* v_l_775_){
_start:
{
lean_object* v___x_776_; 
v___x_776_ = l_Lean_Meta_Sym_Internal_mkLitS___redArg(v_inst_774_, v_l_775_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___redArg(lean_object* v_inst_777_, lean_object* v_declName_778_, lean_object* v_us_779_){
_start:
{
lean_object* v_share1_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
v_share1_780_ = lean_ctor_get(v_inst_777_, 0);
lean_inc(v_share1_780_);
lean_dec_ref(v_inst_777_);
v___x_781_ = l_Lean_Expr_const___override(v_declName_778_, v_us_779_);
v___x_782_ = lean_apply_1(v_share1_780_, v___x_781_);
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS(lean_object* v_m_783_, lean_object* v_inst_784_, lean_object* v_declName_785_, lean_object* v_us_786_){
_start:
{
lean_object* v___x_787_; 
v___x_787_ = l_Lean_Meta_Sym_Internal_mkConstS___redArg(v_inst_784_, v_declName_785_, v_us_786_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___redArg(lean_object* v_inst_788_, lean_object* v_idx_789_){
_start:
{
lean_object* v_share1_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v_share1_790_ = lean_ctor_get(v_inst_788_, 0);
lean_inc(v_share1_790_);
lean_dec_ref(v_inst_788_);
v___x_791_ = l_Lean_Expr_bvar___override(v_idx_789_);
v___x_792_ = lean_apply_1(v_share1_790_, v___x_791_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS(lean_object* v_m_793_, lean_object* v_inst_794_, lean_object* v_idx_795_){
_start:
{
lean_object* v___x_796_; 
v___x_796_ = l_Lean_Meta_Sym_Internal_mkBVarS___redArg(v_inst_794_, v_idx_795_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS___redArg(lean_object* v_inst_797_, lean_object* v_u_798_){
_start:
{
lean_object* v_share1_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
v_share1_799_ = lean_ctor_get(v_inst_797_, 0);
lean_inc(v_share1_799_);
lean_dec_ref(v_inst_797_);
v___x_800_ = l_Lean_Expr_sort___override(v_u_798_);
v___x_801_ = lean_apply_1(v_share1_799_, v___x_800_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS(lean_object* v_m_802_, lean_object* v_inst_803_, lean_object* v_u_804_){
_start:
{
lean_object* v___x_805_; 
v___x_805_ = l_Lean_Meta_Sym_Internal_mkSortS___redArg(v_inst_803_, v_u_804_);
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___redArg(lean_object* v_inst_806_, lean_object* v_fvarId_807_){
_start:
{
lean_object* v_share1_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
v_share1_808_ = lean_ctor_get(v_inst_806_, 0);
lean_inc(v_share1_808_);
lean_dec_ref(v_inst_806_);
v___x_809_ = l_Lean_Expr_fvar___override(v_fvarId_807_);
v___x_810_ = lean_apply_1(v_share1_808_, v___x_809_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS(lean_object* v_m_811_, lean_object* v_inst_812_, lean_object* v_fvarId_813_){
_start:
{
lean_object* v___x_814_; 
v___x_814_ = l_Lean_Meta_Sym_Internal_mkFVarS___redArg(v_inst_812_, v_fvarId_813_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMVarS___redArg(lean_object* v_inst_815_, lean_object* v_mvarId_816_){
_start:
{
lean_object* v_share1_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
v_share1_817_ = lean_ctor_get(v_inst_815_, 0);
lean_inc(v_share1_817_);
lean_dec_ref(v_inst_815_);
v___x_818_ = l_Lean_Expr_mvar___override(v_mvarId_816_);
v___x_819_ = lean_apply_1(v_share1_817_, v___x_818_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMVarS(lean_object* v_m_820_, lean_object* v_inst_821_, lean_object* v_mvarId_822_){
_start:
{
lean_object* v___x_823_; 
v___x_823_ = l_Lean_Meta_Sym_Internal_mkMVarS___redArg(v_inst_821_, v_mvarId_822_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__0(lean_object* v_d_824_, lean_object* v_e_825_, lean_object* v_share1_826_, lean_object* v_____r_827_){
_start:
{
lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_828_ = l_Lean_Expr_mdata___override(v_d_824_, v_e_825_);
v___x_829_ = lean_apply_1(v_share1_826_, v___x_828_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1(lean_object* v___f_830_, lean_object* v_____r_831_){
_start:
{
lean_object* v___x_832_; 
v___x_832_ = lean_apply_1(v___f_830_, v_____r_831_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__2(lean_object* v___f_833_, lean_object* v_assertShared_834_, lean_object* v_e_835_, lean_object* v_toBind_836_, lean_object* v___f_837_, uint8_t v_____do__lift_838_){
_start:
{
if (v_____do__lift_838_ == 0)
{
lean_object* v___x_839_; lean_object* v___x_840_; 
lean_dec(v___f_837_);
lean_dec(v_toBind_836_);
lean_dec_ref(v_e_835_);
lean_dec(v_assertShared_834_);
v___x_839_ = lean_box(0);
v___x_840_ = lean_apply_1(v___f_833_, v___x_839_);
return v___x_840_;
}
else
{
lean_object* v___x_841_; lean_object* v___x_842_; 
lean_dec(v___f_833_);
v___x_841_ = lean_apply_1(v_assertShared_834_, v_e_835_);
v___x_842_ = lean_apply_4(v_toBind_836_, lean_box(0), lean_box(0), v___x_841_, v___f_837_);
return v___x_842_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__2___boxed(lean_object* v___f_843_, lean_object* v_assertShared_844_, lean_object* v_e_845_, lean_object* v_toBind_846_, lean_object* v___f_847_, lean_object* v_____do__lift_848_){
_start:
{
uint8_t v_____do__lift_85__boxed_849_; lean_object* v_res_850_; 
v_____do__lift_85__boxed_849_ = lean_unbox(v_____do__lift_848_);
v_res_850_ = l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__2(v___f_843_, v_assertShared_844_, v_e_845_, v_toBind_846_, v___f_847_, v_____do__lift_85__boxed_849_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg(lean_object* v_inst_851_, lean_object* v_inst_852_, lean_object* v_d_853_, lean_object* v_e_854_){
_start:
{
lean_object* v_toBind_855_; lean_object* v_share1_856_; lean_object* v_assertShared_857_; lean_object* v_isDebugEnabled_858_; lean_object* v___f_859_; lean_object* v___f_860_; lean_object* v___f_861_; lean_object* v___x_862_; 
v_toBind_855_ = lean_ctor_get(v_inst_852_, 1);
lean_inc_n(v_toBind_855_, 2);
lean_dec_ref(v_inst_852_);
v_share1_856_ = lean_ctor_get(v_inst_851_, 0);
lean_inc(v_share1_856_);
v_assertShared_857_ = lean_ctor_get(v_inst_851_, 1);
lean_inc(v_assertShared_857_);
v_isDebugEnabled_858_ = lean_ctor_get(v_inst_851_, 2);
lean_inc(v_isDebugEnabled_858_);
lean_dec_ref(v_inst_851_);
lean_inc_ref(v_e_854_);
v___f_859_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__0), 4, 3);
lean_closure_set(v___f_859_, 0, v_d_853_);
lean_closure_set(v___f_859_, 1, v_e_854_);
lean_closure_set(v___f_859_, 2, v_share1_856_);
lean_inc_ref(v___f_859_);
v___f_860_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_860_, 0, v___f_859_);
v___f_861_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_861_, 0, v___f_859_);
lean_closure_set(v___f_861_, 1, v_assertShared_857_);
lean_closure_set(v___f_861_, 2, v_e_854_);
lean_closure_set(v___f_861_, 3, v_toBind_855_);
lean_closure_set(v___f_861_, 4, v___f_860_);
v___x_862_ = lean_apply_4(v_toBind_855_, lean_box(0), lean_box(0), v_isDebugEnabled_858_, v___f_861_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS(lean_object* v_m_863_, lean_object* v_inst_864_, lean_object* v_inst_865_, lean_object* v_d_866_, lean_object* v_e_867_){
_start:
{
lean_object* v___x_868_; 
v___x_868_ = l_Lean_Meta_Sym_Internal_mkMDataS___redArg(v_inst_864_, v_inst_865_, v_d_866_, v_e_867_);
return v___x_868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__0(lean_object* v_structName_869_, lean_object* v_idx_870_, lean_object* v_struct_871_, lean_object* v_share1_872_, lean_object* v_____r_873_){
_start:
{
lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_874_ = l_Lean_Expr_proj___override(v_structName_869_, v_idx_870_, v_struct_871_);
v___x_875_ = lean_apply_1(v_share1_872_, v___x_874_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__2(lean_object* v___f_876_, lean_object* v_assertShared_877_, lean_object* v_struct_878_, lean_object* v_toBind_879_, lean_object* v___f_880_, uint8_t v_____do__lift_881_){
_start:
{
if (v_____do__lift_881_ == 0)
{
lean_object* v___x_882_; lean_object* v___x_883_; 
lean_dec(v___f_880_);
lean_dec(v_toBind_879_);
lean_dec_ref(v_struct_878_);
lean_dec(v_assertShared_877_);
v___x_882_ = lean_box(0);
v___x_883_ = lean_apply_1(v___f_876_, v___x_882_);
return v___x_883_;
}
else
{
lean_object* v___x_884_; lean_object* v___x_885_; 
lean_dec(v___f_876_);
v___x_884_ = lean_apply_1(v_assertShared_877_, v_struct_878_);
v___x_885_ = lean_apply_4(v_toBind_879_, lean_box(0), lean_box(0), v___x_884_, v___f_880_);
return v___x_885_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__2___boxed(lean_object* v___f_886_, lean_object* v_assertShared_887_, lean_object* v_struct_888_, lean_object* v_toBind_889_, lean_object* v___f_890_, lean_object* v_____do__lift_891_){
_start:
{
uint8_t v_____do__lift_79__boxed_892_; lean_object* v_res_893_; 
v_____do__lift_79__boxed_892_ = lean_unbox(v_____do__lift_891_);
v_res_893_ = l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__2(v___f_886_, v_assertShared_887_, v_struct_888_, v_toBind_889_, v___f_890_, v_____do__lift_79__boxed_892_);
return v_res_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___redArg(lean_object* v_inst_894_, lean_object* v_inst_895_, lean_object* v_structName_896_, lean_object* v_idx_897_, lean_object* v_struct_898_){
_start:
{
lean_object* v_toBind_899_; lean_object* v_share1_900_; lean_object* v_assertShared_901_; lean_object* v_isDebugEnabled_902_; lean_object* v___f_903_; lean_object* v___f_904_; lean_object* v___f_905_; lean_object* v___x_906_; 
v_toBind_899_ = lean_ctor_get(v_inst_895_, 1);
lean_inc_n(v_toBind_899_, 2);
lean_dec_ref(v_inst_895_);
v_share1_900_ = lean_ctor_get(v_inst_894_, 0);
lean_inc(v_share1_900_);
v_assertShared_901_ = lean_ctor_get(v_inst_894_, 1);
lean_inc(v_assertShared_901_);
v_isDebugEnabled_902_ = lean_ctor_get(v_inst_894_, 2);
lean_inc(v_isDebugEnabled_902_);
lean_dec_ref(v_inst_894_);
lean_inc_ref(v_struct_898_);
v___f_903_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__0), 5, 4);
lean_closure_set(v___f_903_, 0, v_structName_896_);
lean_closure_set(v___f_903_, 1, v_idx_897_);
lean_closure_set(v___f_903_, 2, v_struct_898_);
lean_closure_set(v___f_903_, 3, v_share1_900_);
lean_inc_ref(v___f_903_);
v___f_904_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_904_, 0, v___f_903_);
v___f_905_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_905_, 0, v___f_903_);
lean_closure_set(v___f_905_, 1, v_assertShared_901_);
lean_closure_set(v___f_905_, 2, v_struct_898_);
lean_closure_set(v___f_905_, 3, v_toBind_899_);
lean_closure_set(v___f_905_, 4, v___f_904_);
v___x_906_ = lean_apply_4(v_toBind_899_, lean_box(0), lean_box(0), v_isDebugEnabled_902_, v___f_905_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS(lean_object* v_m_907_, lean_object* v_inst_908_, lean_object* v_inst_909_, lean_object* v_structName_910_, lean_object* v_idx_911_, lean_object* v_struct_912_){
_start:
{
lean_object* v___x_913_; 
v___x_913_ = l_Lean_Meta_Sym_Internal_mkProjS___redArg(v_inst_908_, v_inst_909_, v_structName_910_, v_idx_911_, v_struct_912_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__0(lean_object* v_f_914_, lean_object* v_a_915_, lean_object* v_share1_916_, lean_object* v_____r_917_){
_start:
{
lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_918_ = l_Lean_Expr_app___override(v_f_914_, v_a_915_);
v___x_919_ = lean_apply_1(v_share1_916_, v___x_918_);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__2(lean_object* v_assertShared_920_, lean_object* v_a_921_, lean_object* v_toBind_922_, lean_object* v___f_923_, lean_object* v_____r_924_){
_start:
{
lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_925_ = lean_apply_1(v_assertShared_920_, v_a_921_);
v___x_926_ = lean_apply_4(v_toBind_922_, lean_box(0), lean_box(0), v___x_925_, v___f_923_);
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__1(lean_object* v___f_927_, lean_object* v_assertShared_928_, lean_object* v_a_929_, lean_object* v_toBind_930_, lean_object* v___f_931_, lean_object* v_f_932_, uint8_t v_____do__lift_933_){
_start:
{
if (v_____do__lift_933_ == 0)
{
lean_object* v___x_934_; lean_object* v___x_935_; 
lean_dec_ref(v_f_932_);
lean_dec(v___f_931_);
lean_dec(v_toBind_930_);
lean_dec_ref(v_a_929_);
lean_dec(v_assertShared_928_);
v___x_934_ = lean_box(0);
v___x_935_ = lean_apply_1(v___f_927_, v___x_934_);
return v___x_935_;
}
else
{
lean_object* v___f_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
lean_dec(v___f_927_);
lean_inc(v_toBind_930_);
lean_inc(v_assertShared_928_);
v___f_936_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__2), 5, 4);
lean_closure_set(v___f_936_, 0, v_assertShared_928_);
lean_closure_set(v___f_936_, 1, v_a_929_);
lean_closure_set(v___f_936_, 2, v_toBind_930_);
lean_closure_set(v___f_936_, 3, v___f_931_);
v___x_937_ = lean_apply_1(v_assertShared_928_, v_f_932_);
v___x_938_ = lean_apply_4(v_toBind_930_, lean_box(0), lean_box(0), v___x_937_, v___f_936_);
return v___x_938_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__1___boxed(lean_object* v___f_939_, lean_object* v_assertShared_940_, lean_object* v_a_941_, lean_object* v_toBind_942_, lean_object* v___f_943_, lean_object* v_f_944_, lean_object* v_____do__lift_945_){
_start:
{
uint8_t v_____do__lift_104__boxed_946_; lean_object* v_res_947_; 
v_____do__lift_104__boxed_946_ = lean_unbox(v_____do__lift_945_);
v_res_947_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__1(v___f_939_, v_assertShared_940_, v_a_941_, v_toBind_942_, v___f_943_, v_f_944_, v_____do__lift_104__boxed_946_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg(lean_object* v_inst_948_, lean_object* v_inst_949_, lean_object* v_f_950_, lean_object* v_a_951_){
_start:
{
lean_object* v_toBind_952_; lean_object* v_share1_953_; lean_object* v_assertShared_954_; lean_object* v_isDebugEnabled_955_; lean_object* v___f_956_; lean_object* v___f_957_; lean_object* v___f_958_; lean_object* v___x_959_; 
v_toBind_952_ = lean_ctor_get(v_inst_949_, 1);
lean_inc_n(v_toBind_952_, 2);
lean_dec_ref(v_inst_949_);
v_share1_953_ = lean_ctor_get(v_inst_948_, 0);
lean_inc(v_share1_953_);
v_assertShared_954_ = lean_ctor_get(v_inst_948_, 1);
lean_inc(v_assertShared_954_);
v_isDebugEnabled_955_ = lean_ctor_get(v_inst_948_, 2);
lean_inc(v_isDebugEnabled_955_);
lean_dec_ref(v_inst_948_);
lean_inc_ref(v_a_951_);
lean_inc_ref(v_f_950_);
v___f_956_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__0), 4, 3);
lean_closure_set(v___f_956_, 0, v_f_950_);
lean_closure_set(v___f_956_, 1, v_a_951_);
lean_closure_set(v___f_956_, 2, v_share1_953_);
lean_inc_ref(v___f_956_);
v___f_957_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_957_, 0, v___f_956_);
v___f_958_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_958_, 0, v___f_956_);
lean_closure_set(v___f_958_, 1, v_assertShared_954_);
lean_closure_set(v___f_958_, 2, v_a_951_);
lean_closure_set(v___f_958_, 3, v_toBind_952_);
lean_closure_set(v___f_958_, 4, v___f_957_);
lean_closure_set(v___f_958_, 5, v_f_950_);
v___x_959_ = lean_apply_4(v_toBind_952_, lean_box(0), lean_box(0), v_isDebugEnabled_955_, v___f_958_);
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS(lean_object* v_m_960_, lean_object* v_inst_961_, lean_object* v_inst_962_, lean_object* v_f_963_, lean_object* v_a_964_){
_start:
{
lean_object* v___x_965_; 
v___x_965_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_961_, v_inst_962_, v_f_963_, v_a_964_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__0(lean_object* v_x_966_, lean_object* v_t_967_, lean_object* v_b_968_, uint8_t v_bi_969_, lean_object* v_share1_970_, lean_object* v_____r_971_){
_start:
{
lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_972_ = l_Lean_Expr_lam___override(v_x_966_, v_t_967_, v_b_968_, v_bi_969_);
v___x_973_ = lean_apply_1(v_share1_970_, v___x_972_);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__0___boxed(lean_object* v_x_974_, lean_object* v_t_975_, lean_object* v_b_976_, lean_object* v_bi_977_, lean_object* v_share1_978_, lean_object* v_____r_979_){
_start:
{
uint8_t v_bi_boxed_980_; lean_object* v_res_981_; 
v_bi_boxed_980_ = lean_unbox(v_bi_977_);
v_res_981_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__0(v_x_974_, v_t_975_, v_b_976_, v_bi_boxed_980_, v_share1_978_, v_____r_979_);
return v_res_981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__2(lean_object* v_assertShared_982_, lean_object* v_b_983_, lean_object* v_toBind_984_, lean_object* v___f_985_, lean_object* v_____r_986_){
_start:
{
lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_987_ = lean_apply_1(v_assertShared_982_, v_b_983_);
v___x_988_ = lean_apply_4(v_toBind_984_, lean_box(0), lean_box(0), v___x_987_, v___f_985_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1(lean_object* v___f_989_, lean_object* v_assertShared_990_, lean_object* v_b_991_, lean_object* v_toBind_992_, lean_object* v___f_993_, lean_object* v_t_994_, uint8_t v_____do__lift_995_){
_start:
{
if (v_____do__lift_995_ == 0)
{
lean_object* v___x_996_; lean_object* v___x_997_; 
lean_dec_ref(v_t_994_);
lean_dec(v___f_993_);
lean_dec(v_toBind_992_);
lean_dec_ref(v_b_991_);
lean_dec(v_assertShared_990_);
v___x_996_ = lean_box(0);
v___x_997_ = lean_apply_1(v___f_989_, v___x_996_);
return v___x_997_;
}
else
{
lean_object* v___f_998_; lean_object* v___x_999_; lean_object* v___x_1000_; 
lean_dec(v___f_989_);
lean_inc(v_toBind_992_);
lean_inc(v_assertShared_990_);
v___f_998_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__2), 5, 4);
lean_closure_set(v___f_998_, 0, v_assertShared_990_);
lean_closure_set(v___f_998_, 1, v_b_991_);
lean_closure_set(v___f_998_, 2, v_toBind_992_);
lean_closure_set(v___f_998_, 3, v___f_993_);
v___x_999_ = lean_apply_1(v_assertShared_990_, v_t_994_);
v___x_1000_ = lean_apply_4(v_toBind_992_, lean_box(0), lean_box(0), v___x_999_, v___f_998_);
return v___x_1000_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1___boxed(lean_object* v___f_1001_, lean_object* v_assertShared_1002_, lean_object* v_b_1003_, lean_object* v_toBind_1004_, lean_object* v___f_1005_, lean_object* v_t_1006_, lean_object* v_____do__lift_1007_){
_start:
{
uint8_t v_____do__lift_105__boxed_1008_; lean_object* v_res_1009_; 
v_____do__lift_105__boxed_1008_ = lean_unbox(v_____do__lift_1007_);
v_res_1009_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1(v___f_1001_, v_assertShared_1002_, v_b_1003_, v_toBind_1004_, v___f_1005_, v_t_1006_, v_____do__lift_105__boxed_1008_);
return v_res_1009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(lean_object* v_inst_1010_, lean_object* v_inst_1011_, lean_object* v_x_1012_, uint8_t v_bi_1013_, lean_object* v_t_1014_, lean_object* v_b_1015_){
_start:
{
lean_object* v_toBind_1016_; lean_object* v_share1_1017_; lean_object* v_assertShared_1018_; lean_object* v_isDebugEnabled_1019_; lean_object* v___x_1020_; lean_object* v___f_1021_; lean_object* v___f_1022_; lean_object* v___f_1023_; lean_object* v___x_1024_; 
v_toBind_1016_ = lean_ctor_get(v_inst_1011_, 1);
lean_inc_n(v_toBind_1016_, 2);
lean_dec_ref(v_inst_1011_);
v_share1_1017_ = lean_ctor_get(v_inst_1010_, 0);
lean_inc(v_share1_1017_);
v_assertShared_1018_ = lean_ctor_get(v_inst_1010_, 1);
lean_inc(v_assertShared_1018_);
v_isDebugEnabled_1019_ = lean_ctor_get(v_inst_1010_, 2);
lean_inc(v_isDebugEnabled_1019_);
lean_dec_ref(v_inst_1010_);
v___x_1020_ = lean_box(v_bi_1013_);
lean_inc_ref(v_b_1015_);
lean_inc_ref(v_t_1014_);
v___f_1021_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1021_, 0, v_x_1012_);
lean_closure_set(v___f_1021_, 1, v_t_1014_);
lean_closure_set(v___f_1021_, 2, v_b_1015_);
lean_closure_set(v___f_1021_, 3, v___x_1020_);
lean_closure_set(v___f_1021_, 4, v_share1_1017_);
lean_inc_ref(v___f_1021_);
v___f_1022_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1022_, 0, v___f_1021_);
v___f_1023_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_1023_, 0, v___f_1021_);
lean_closure_set(v___f_1023_, 1, v_assertShared_1018_);
lean_closure_set(v___f_1023_, 2, v_b_1015_);
lean_closure_set(v___f_1023_, 3, v_toBind_1016_);
lean_closure_set(v___f_1023_, 4, v___f_1022_);
lean_closure_set(v___f_1023_, 5, v_t_1014_);
v___x_1024_ = lean_apply_4(v_toBind_1016_, lean_box(0), lean_box(0), v_isDebugEnabled_1019_, v___f_1023_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___boxed(lean_object* v_inst_1025_, lean_object* v_inst_1026_, lean_object* v_x_1027_, lean_object* v_bi_1028_, lean_object* v_t_1029_, lean_object* v_b_1030_){
_start:
{
uint8_t v_bi_boxed_1031_; lean_object* v_res_1032_; 
v_bi_boxed_1031_ = lean_unbox(v_bi_1028_);
v_res_1032_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v_inst_1025_, v_inst_1026_, v_x_1027_, v_bi_boxed_1031_, v_t_1029_, v_b_1030_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS(lean_object* v_m_1033_, lean_object* v_inst_1034_, lean_object* v_inst_1035_, lean_object* v_x_1036_, uint8_t v_bi_1037_, lean_object* v_t_1038_, lean_object* v_b_1039_){
_start:
{
lean_object* v___x_1040_; 
v___x_1040_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v_inst_1034_, v_inst_1035_, v_x_1036_, v_bi_1037_, v_t_1038_, v_b_1039_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___boxed(lean_object* v_m_1041_, lean_object* v_inst_1042_, lean_object* v_inst_1043_, lean_object* v_x_1044_, lean_object* v_bi_1045_, lean_object* v_t_1046_, lean_object* v_b_1047_){
_start:
{
uint8_t v_bi_boxed_1048_; lean_object* v_res_1049_; 
v_bi_boxed_1048_ = lean_unbox(v_bi_1045_);
v_res_1049_ = l_Lean_Meta_Sym_Internal_mkLambdaS(v_m_1041_, v_inst_1042_, v_inst_1043_, v_x_1044_, v_bi_boxed_1048_, v_t_1046_, v_b_1047_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___redArg___lam__0(lean_object* v_x_1050_, lean_object* v_t_1051_, lean_object* v_b_1052_, uint8_t v_bi_1053_, lean_object* v_share1_1054_, lean_object* v_____r_1055_){
_start:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1056_ = l_Lean_Expr_forallE___override(v_x_1050_, v_t_1051_, v_b_1052_, v_bi_1053_);
v___x_1057_ = lean_apply_1(v_share1_1054_, v___x_1056_);
return v___x_1057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___redArg___lam__0___boxed(lean_object* v_x_1058_, lean_object* v_t_1059_, lean_object* v_b_1060_, lean_object* v_bi_1061_, lean_object* v_share1_1062_, lean_object* v_____r_1063_){
_start:
{
uint8_t v_bi_boxed_1064_; lean_object* v_res_1065_; 
v_bi_boxed_1064_ = lean_unbox(v_bi_1061_);
v_res_1065_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg___lam__0(v_x_1058_, v_t_1059_, v_b_1060_, v_bi_boxed_1064_, v_share1_1062_, v_____r_1063_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___redArg(lean_object* v_inst_1066_, lean_object* v_inst_1067_, lean_object* v_x_1068_, uint8_t v_bi_1069_, lean_object* v_t_1070_, lean_object* v_b_1071_){
_start:
{
lean_object* v_toBind_1072_; lean_object* v_share1_1073_; lean_object* v_assertShared_1074_; lean_object* v_isDebugEnabled_1075_; lean_object* v___x_1076_; lean_object* v___f_1077_; lean_object* v___f_1078_; lean_object* v___f_1079_; lean_object* v___x_1080_; 
v_toBind_1072_ = lean_ctor_get(v_inst_1067_, 1);
lean_inc_n(v_toBind_1072_, 2);
lean_dec_ref(v_inst_1067_);
v_share1_1073_ = lean_ctor_get(v_inst_1066_, 0);
lean_inc(v_share1_1073_);
v_assertShared_1074_ = lean_ctor_get(v_inst_1066_, 1);
lean_inc(v_assertShared_1074_);
v_isDebugEnabled_1075_ = lean_ctor_get(v_inst_1066_, 2);
lean_inc(v_isDebugEnabled_1075_);
lean_dec_ref(v_inst_1066_);
v___x_1076_ = lean_box(v_bi_1069_);
lean_inc_ref(v_b_1071_);
lean_inc_ref(v_t_1070_);
v___f_1077_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkForallS___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1077_, 0, v_x_1068_);
lean_closure_set(v___f_1077_, 1, v_t_1070_);
lean_closure_set(v___f_1077_, 2, v_b_1071_);
lean_closure_set(v___f_1077_, 3, v___x_1076_);
lean_closure_set(v___f_1077_, 4, v_share1_1073_);
lean_inc_ref(v___f_1077_);
v___f_1078_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1078_, 0, v___f_1077_);
v___f_1079_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_1079_, 0, v___f_1077_);
lean_closure_set(v___f_1079_, 1, v_assertShared_1074_);
lean_closure_set(v___f_1079_, 2, v_b_1071_);
lean_closure_set(v___f_1079_, 3, v_toBind_1072_);
lean_closure_set(v___f_1079_, 4, v___f_1078_);
lean_closure_set(v___f_1079_, 5, v_t_1070_);
v___x_1080_ = lean_apply_4(v_toBind_1072_, lean_box(0), lean_box(0), v_isDebugEnabled_1075_, v___f_1079_);
return v___x_1080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___redArg___boxed(lean_object* v_inst_1081_, lean_object* v_inst_1082_, lean_object* v_x_1083_, lean_object* v_bi_1084_, lean_object* v_t_1085_, lean_object* v_b_1086_){
_start:
{
uint8_t v_bi_boxed_1087_; lean_object* v_res_1088_; 
v_bi_boxed_1087_ = lean_unbox(v_bi_1084_);
v_res_1088_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v_inst_1081_, v_inst_1082_, v_x_1083_, v_bi_boxed_1087_, v_t_1085_, v_b_1086_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS(lean_object* v_m_1089_, lean_object* v_inst_1090_, lean_object* v_inst_1091_, lean_object* v_x_1092_, uint8_t v_bi_1093_, lean_object* v_t_1094_, lean_object* v_b_1095_){
_start:
{
lean_object* v___x_1096_; 
v___x_1096_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v_inst_1090_, v_inst_1091_, v_x_1092_, v_bi_1093_, v_t_1094_, v_b_1095_);
return v___x_1096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___boxed(lean_object* v_m_1097_, lean_object* v_inst_1098_, lean_object* v_inst_1099_, lean_object* v_x_1100_, lean_object* v_bi_1101_, lean_object* v_t_1102_, lean_object* v_b_1103_){
_start:
{
uint8_t v_bi_boxed_1104_; lean_object* v_res_1105_; 
v_bi_boxed_1104_ = lean_unbox(v_bi_1101_);
v_res_1105_ = l_Lean_Meta_Sym_Internal_mkForallS(v_m_1097_, v_inst_1098_, v_inst_1099_, v_x_1100_, v_bi_boxed_1104_, v_t_1102_, v_b_1103_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__0(lean_object* v_x_1106_, lean_object* v_t_1107_, lean_object* v_v_1108_, lean_object* v_b_1109_, uint8_t v_nondep_1110_, lean_object* v_share1_1111_, lean_object* v_____r_1112_){
_start:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1113_ = l_Lean_Expr_letE___override(v_x_1106_, v_t_1107_, v_v_1108_, v_b_1109_, v_nondep_1110_);
v___x_1114_ = lean_apply_1(v_share1_1111_, v___x_1113_);
return v___x_1114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__0___boxed(lean_object* v_x_1115_, lean_object* v_t_1116_, lean_object* v_v_1117_, lean_object* v_b_1118_, lean_object* v_nondep_1119_, lean_object* v_share1_1120_, lean_object* v_____r_1121_){
_start:
{
uint8_t v_nondep_boxed_1122_; lean_object* v_res_1123_; 
v_nondep_boxed_1122_ = lean_unbox(v_nondep_1119_);
v_res_1123_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__0(v_x_1115_, v_t_1116_, v_v_1117_, v_b_1118_, v_nondep_boxed_1122_, v_share1_1120_, v_____r_1121_);
return v_res_1123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__3(lean_object* v_assertShared_1124_, lean_object* v_v_1125_, lean_object* v_toBind_1126_, lean_object* v___f_1127_, lean_object* v_____r_1128_){
_start:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1129_ = lean_apply_1(v_assertShared_1124_, v_v_1125_);
v___x_1130_ = lean_apply_4(v_toBind_1126_, lean_box(0), lean_box(0), v___x_1129_, v___f_1127_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1(lean_object* v___f_1131_, lean_object* v_assertShared_1132_, lean_object* v_b_1133_, lean_object* v_toBind_1134_, lean_object* v___f_1135_, lean_object* v_v_1136_, lean_object* v_t_1137_, uint8_t v_____do__lift_1138_){
_start:
{
if (v_____do__lift_1138_ == 0)
{
lean_object* v___x_1139_; lean_object* v___x_1140_; 
lean_dec_ref(v_t_1137_);
lean_dec_ref(v_v_1136_);
lean_dec(v___f_1135_);
lean_dec(v_toBind_1134_);
lean_dec_ref(v_b_1133_);
lean_dec(v_assertShared_1132_);
v___x_1139_ = lean_box(0);
v___x_1140_ = lean_apply_1(v___f_1131_, v___x_1139_);
return v___x_1140_;
}
else
{
lean_object* v___f_1141_; lean_object* v___f_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
lean_dec(v___f_1131_);
lean_inc_n(v_toBind_1134_, 2);
lean_inc_n(v_assertShared_1132_, 2);
v___f_1141_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__2), 5, 4);
lean_closure_set(v___f_1141_, 0, v_assertShared_1132_);
lean_closure_set(v___f_1141_, 1, v_b_1133_);
lean_closure_set(v___f_1141_, 2, v_toBind_1134_);
lean_closure_set(v___f_1141_, 3, v___f_1135_);
v___f_1142_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__3), 5, 4);
lean_closure_set(v___f_1142_, 0, v_assertShared_1132_);
lean_closure_set(v___f_1142_, 1, v_v_1136_);
lean_closure_set(v___f_1142_, 2, v_toBind_1134_);
lean_closure_set(v___f_1142_, 3, v___f_1141_);
v___x_1143_ = lean_apply_1(v_assertShared_1132_, v_t_1137_);
v___x_1144_ = lean_apply_4(v_toBind_1134_, lean_box(0), lean_box(0), v___x_1143_, v___f_1142_);
return v___x_1144_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1___boxed(lean_object* v___f_1145_, lean_object* v_assertShared_1146_, lean_object* v_b_1147_, lean_object* v_toBind_1148_, lean_object* v___f_1149_, lean_object* v_v_1150_, lean_object* v_t_1151_, lean_object* v_____do__lift_1152_){
_start:
{
uint8_t v_____do__lift_122__boxed_1153_; lean_object* v_res_1154_; 
v_____do__lift_122__boxed_1153_ = lean_unbox(v_____do__lift_1152_);
v_res_1154_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1(v___f_1145_, v_assertShared_1146_, v_b_1147_, v_toBind_1148_, v___f_1149_, v_v_1150_, v_t_1151_, v_____do__lift_122__boxed_1153_);
return v_res_1154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg(lean_object* v_inst_1155_, lean_object* v_inst_1156_, lean_object* v_x_1157_, lean_object* v_t_1158_, lean_object* v_v_1159_, lean_object* v_b_1160_, uint8_t v_nondep_1161_){
_start:
{
lean_object* v_toBind_1162_; lean_object* v_share1_1163_; lean_object* v_assertShared_1164_; lean_object* v_isDebugEnabled_1165_; lean_object* v___x_1166_; lean_object* v___f_1167_; lean_object* v___f_1168_; lean_object* v___f_1169_; lean_object* v___x_1170_; 
v_toBind_1162_ = lean_ctor_get(v_inst_1156_, 1);
lean_inc_n(v_toBind_1162_, 2);
lean_dec_ref(v_inst_1156_);
v_share1_1163_ = lean_ctor_get(v_inst_1155_, 0);
lean_inc(v_share1_1163_);
v_assertShared_1164_ = lean_ctor_get(v_inst_1155_, 1);
lean_inc(v_assertShared_1164_);
v_isDebugEnabled_1165_ = lean_ctor_get(v_inst_1155_, 2);
lean_inc(v_isDebugEnabled_1165_);
lean_dec_ref(v_inst_1155_);
v___x_1166_ = lean_box(v_nondep_1161_);
lean_inc_ref(v_b_1160_);
lean_inc_ref(v_v_1159_);
lean_inc_ref(v_t_1158_);
v___f_1167_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_1167_, 0, v_x_1157_);
lean_closure_set(v___f_1167_, 1, v_t_1158_);
lean_closure_set(v___f_1167_, 2, v_v_1159_);
lean_closure_set(v___f_1167_, 3, v_b_1160_);
lean_closure_set(v___f_1167_, 4, v___x_1166_);
lean_closure_set(v___f_1167_, 5, v_share1_1163_);
lean_inc_ref(v___f_1167_);
v___f_1168_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1168_, 0, v___f_1167_);
v___f_1169_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_1169_, 0, v___f_1167_);
lean_closure_set(v___f_1169_, 1, v_assertShared_1164_);
lean_closure_set(v___f_1169_, 2, v_b_1160_);
lean_closure_set(v___f_1169_, 3, v_toBind_1162_);
lean_closure_set(v___f_1169_, 4, v___f_1168_);
lean_closure_set(v___f_1169_, 5, v_v_1159_);
lean_closure_set(v___f_1169_, 6, v_t_1158_);
v___x_1170_ = lean_apply_4(v_toBind_1162_, lean_box(0), lean_box(0), v_isDebugEnabled_1165_, v___f_1169_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___boxed(lean_object* v_inst_1171_, lean_object* v_inst_1172_, lean_object* v_x_1173_, lean_object* v_t_1174_, lean_object* v_v_1175_, lean_object* v_b_1176_, lean_object* v_nondep_1177_){
_start:
{
uint8_t v_nondep_boxed_1178_; lean_object* v_res_1179_; 
v_nondep_boxed_1178_ = lean_unbox(v_nondep_1177_);
v_res_1179_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1171_, v_inst_1172_, v_x_1173_, v_t_1174_, v_v_1175_, v_b_1176_, v_nondep_boxed_1178_);
return v_res_1179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS(lean_object* v_m_1180_, lean_object* v_inst_1181_, lean_object* v_inst_1182_, lean_object* v_x_1183_, lean_object* v_t_1184_, lean_object* v_v_1185_, lean_object* v_b_1186_, uint8_t v_nondep_1187_){
_start:
{
lean_object* v___x_1188_; 
v___x_1188_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1181_, v_inst_1182_, v_x_1183_, v_t_1184_, v_v_1185_, v_b_1186_, v_nondep_1187_);
return v___x_1188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___boxed(lean_object* v_m_1189_, lean_object* v_inst_1190_, lean_object* v_inst_1191_, lean_object* v_x_1192_, lean_object* v_t_1193_, lean_object* v_v_1194_, lean_object* v_b_1195_, lean_object* v_nondep_1196_){
_start:
{
uint8_t v_nondep_boxed_1197_; lean_object* v_res_1198_; 
v_nondep_boxed_1197_ = lean_unbox(v_nondep_1196_);
v_res_1198_ = l_Lean_Meta_Sym_Internal_mkLetS(v_m_1189_, v_inst_1190_, v_inst_1191_, v_x_1192_, v_t_1193_, v_v_1194_, v_b_1195_, v_nondep_boxed_1197_);
return v_res_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkHaveS___redArg___lam__0(lean_object* v_x_1199_, lean_object* v_t_1200_, lean_object* v_v_1201_, lean_object* v_b_1202_, lean_object* v_share1_1203_, lean_object* v_____r_1204_){
_start:
{
uint8_t v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; 
v___x_1205_ = 1;
v___x_1206_ = l_Lean_Expr_letE___override(v_x_1199_, v_t_1200_, v_v_1201_, v_b_1202_, v___x_1205_);
v___x_1207_ = lean_apply_1(v_share1_1203_, v___x_1206_);
return v___x_1207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkHaveS___redArg(lean_object* v_inst_1208_, lean_object* v_inst_1209_, lean_object* v_x_1210_, lean_object* v_t_1211_, lean_object* v_v_1212_, lean_object* v_b_1213_){
_start:
{
lean_object* v_toBind_1214_; lean_object* v_share1_1215_; lean_object* v_assertShared_1216_; lean_object* v_isDebugEnabled_1217_; lean_object* v___f_1218_; lean_object* v___f_1219_; lean_object* v___f_1220_; lean_object* v___x_1221_; 
v_toBind_1214_ = lean_ctor_get(v_inst_1209_, 1);
lean_inc_n(v_toBind_1214_, 2);
lean_dec_ref(v_inst_1209_);
v_share1_1215_ = lean_ctor_get(v_inst_1208_, 0);
lean_inc(v_share1_1215_);
v_assertShared_1216_ = lean_ctor_get(v_inst_1208_, 1);
lean_inc(v_assertShared_1216_);
v_isDebugEnabled_1217_ = lean_ctor_get(v_inst_1208_, 2);
lean_inc(v_isDebugEnabled_1217_);
lean_dec_ref(v_inst_1208_);
lean_inc_ref(v_b_1213_);
lean_inc_ref(v_v_1212_);
lean_inc_ref(v_t_1211_);
v___f_1218_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkHaveS___redArg___lam__0), 6, 5);
lean_closure_set(v___f_1218_, 0, v_x_1210_);
lean_closure_set(v___f_1218_, 1, v_t_1211_);
lean_closure_set(v___f_1218_, 2, v_v_1212_);
lean_closure_set(v___f_1218_, 3, v_b_1213_);
lean_closure_set(v___f_1218_, 4, v_share1_1215_);
lean_inc_ref(v___f_1218_);
v___f_1219_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1219_, 0, v___f_1218_);
v___f_1220_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_1220_, 0, v___f_1218_);
lean_closure_set(v___f_1220_, 1, v_assertShared_1216_);
lean_closure_set(v___f_1220_, 2, v_b_1213_);
lean_closure_set(v___f_1220_, 3, v_toBind_1214_);
lean_closure_set(v___f_1220_, 4, v___f_1219_);
lean_closure_set(v___f_1220_, 5, v_v_1212_);
lean_closure_set(v___f_1220_, 6, v_t_1211_);
v___x_1221_ = lean_apply_4(v_toBind_1214_, lean_box(0), lean_box(0), v_isDebugEnabled_1217_, v___f_1220_);
return v___x_1221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkHaveS(lean_object* v_m_1222_, lean_object* v_inst_1223_, lean_object* v_inst_1224_, lean_object* v_x_1225_, lean_object* v_t_1226_, lean_object* v_v_1227_, lean_object* v_b_1228_){
_start:
{
lean_object* v___x_1229_; 
v___x_1229_ = l_Lean_Meta_Sym_Internal_mkHaveS___redArg(v_inst_1223_, v_inst_1224_, v_x_1225_, v_t_1226_, v_v_1227_, v_b_1228_);
return v___x_1229_;
}
}
static lean_object* _init_l_Lean_Expr_updateAppS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1232_ = ((lean_object*)(l_Lean_Expr_updateAppS_x21___redArg___closed__1));
v___x_1233_ = lean_unsigned_to_nat(25u);
v___x_1234_ = lean_unsigned_to_nat(148u);
v___x_1235_ = ((lean_object*)(l_Lean_Expr_updateAppS_x21___redArg___closed__0));
v___x_1236_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1237_ = l_mkPanicMessageWithDecl(v___x_1236_, v___x_1235_, v___x_1234_, v___x_1233_, v___x_1232_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateAppS_x21___redArg(lean_object* v_inst_1238_, lean_object* v_inst_1239_, lean_object* v_e_1240_, lean_object* v_newFn_1241_, lean_object* v_newArg_1242_){
_start:
{
uint8_t v___y_1244_; 
if (lean_obj_tag(v_e_1240_) == 5)
{
lean_object* v_fn_1249_; lean_object* v_arg_1250_; uint8_t v___x_1251_; 
v_fn_1249_ = lean_ctor_get(v_e_1240_, 0);
v_arg_1250_ = lean_ctor_get(v_e_1240_, 1);
v___x_1251_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fn_1249_, v_newFn_1241_);
if (v___x_1251_ == 0)
{
v___y_1244_ = v___x_1251_;
goto v___jp_1243_;
}
else
{
uint8_t v___x_1252_; 
v___x_1252_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_1250_, v_newArg_1242_);
v___y_1244_ = v___x_1252_;
goto v___jp_1243_;
}
}
else
{
lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; 
lean_dec_ref(v_newArg_1242_);
lean_dec_ref(v_newFn_1241_);
lean_dec_ref(v_e_1240_);
lean_dec_ref(v_inst_1238_);
v___x_1253_ = l_Lean_instInhabitedExpr;
v___x_1254_ = l_instInhabitedOfMonad___redArg(v_inst_1239_, v___x_1253_);
v___x_1255_ = lean_obj_once(&l_Lean_Expr_updateAppS_x21___redArg___closed__2, &l_Lean_Expr_updateAppS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateAppS_x21___redArg___closed__2);
v___x_1256_ = l_panic___redArg(v___x_1254_, v___x_1255_);
lean_dec(v___x_1254_);
return v___x_1256_;
}
v___jp_1243_:
{
if (v___y_1244_ == 0)
{
lean_object* v___x_1245_; 
lean_dec_ref(v_e_1240_);
v___x_1245_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1238_, v_inst_1239_, v_newFn_1241_, v_newArg_1242_);
return v___x_1245_;
}
else
{
lean_object* v_toApplicative_1246_; lean_object* v_toPure_1247_; lean_object* v___x_1248_; 
lean_dec_ref(v_newArg_1242_);
lean_dec_ref(v_newFn_1241_);
lean_dec_ref(v_inst_1238_);
v_toApplicative_1246_ = lean_ctor_get(v_inst_1239_, 0);
lean_inc_ref(v_toApplicative_1246_);
lean_dec_ref(v_inst_1239_);
v_toPure_1247_ = lean_ctor_get(v_toApplicative_1246_, 1);
lean_inc(v_toPure_1247_);
lean_dec_ref(v_toApplicative_1246_);
v___x_1248_ = lean_apply_2(v_toPure_1247_, lean_box(0), v_e_1240_);
return v___x_1248_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateAppS_x21(lean_object* v_m_1257_, lean_object* v_inst_1258_, lean_object* v_inst_1259_, lean_object* v_e_1260_, lean_object* v_newFn_1261_, lean_object* v_newArg_1262_){
_start:
{
uint8_t v___y_1264_; 
if (lean_obj_tag(v_e_1260_) == 5)
{
lean_object* v_fn_1269_; lean_object* v_arg_1270_; uint8_t v___x_1271_; 
v_fn_1269_ = lean_ctor_get(v_e_1260_, 0);
v_arg_1270_ = lean_ctor_get(v_e_1260_, 1);
v___x_1271_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fn_1269_, v_newFn_1261_);
if (v___x_1271_ == 0)
{
v___y_1264_ = v___x_1271_;
goto v___jp_1263_;
}
else
{
uint8_t v___x_1272_; 
v___x_1272_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_1270_, v_newArg_1262_);
v___y_1264_ = v___x_1272_;
goto v___jp_1263_;
}
}
else
{
lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; 
lean_dec_ref(v_newArg_1262_);
lean_dec_ref(v_newFn_1261_);
lean_dec_ref(v_e_1260_);
lean_dec_ref(v_inst_1258_);
v___x_1273_ = l_Lean_instInhabitedExpr;
v___x_1274_ = l_instInhabitedOfMonad___redArg(v_inst_1259_, v___x_1273_);
v___x_1275_ = lean_obj_once(&l_Lean_Expr_updateAppS_x21___redArg___closed__2, &l_Lean_Expr_updateAppS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateAppS_x21___redArg___closed__2);
v___x_1276_ = l_panic___redArg(v___x_1274_, v___x_1275_);
lean_dec(v___x_1274_);
return v___x_1276_;
}
v___jp_1263_:
{
if (v___y_1264_ == 0)
{
lean_object* v___x_1265_; 
lean_dec_ref(v_e_1260_);
v___x_1265_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1258_, v_inst_1259_, v_newFn_1261_, v_newArg_1262_);
return v___x_1265_;
}
else
{
lean_object* v_toApplicative_1266_; lean_object* v_toPure_1267_; lean_object* v___x_1268_; 
lean_dec_ref(v_newArg_1262_);
lean_dec_ref(v_newFn_1261_);
lean_dec_ref(v_inst_1258_);
v_toApplicative_1266_ = lean_ctor_get(v_inst_1259_, 0);
lean_inc_ref(v_toApplicative_1266_);
lean_dec_ref(v_inst_1259_);
v_toPure_1267_ = lean_ctor_get(v_toApplicative_1266_, 1);
lean_inc(v_toPure_1267_);
lean_dec_ref(v_toApplicative_1266_);
v___x_1268_ = lean_apply_2(v_toPure_1267_, lean_box(0), v_e_1260_);
return v___x_1268_;
}
}
}
}
static lean_object* _init_l_Lean_Expr_updateMDataS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1279_ = ((lean_object*)(l_Lean_Expr_updateMDataS_x21___redArg___closed__1));
v___x_1280_ = lean_unsigned_to_nat(24u);
v___x_1281_ = lean_unsigned_to_nat(152u);
v___x_1282_ = ((lean_object*)(l_Lean_Expr_updateMDataS_x21___redArg___closed__0));
v___x_1283_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1284_ = l_mkPanicMessageWithDecl(v___x_1283_, v___x_1282_, v___x_1281_, v___x_1280_, v___x_1279_);
return v___x_1284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateMDataS_x21___redArg(lean_object* v_inst_1285_, lean_object* v_inst_1286_, lean_object* v_e_1287_, lean_object* v_newExpr_1288_){
_start:
{
if (lean_obj_tag(v_e_1287_) == 10)
{
lean_object* v_data_1289_; lean_object* v_expr_1290_; uint8_t v___x_1291_; 
v_data_1289_ = lean_ctor_get(v_e_1287_, 0);
v_expr_1290_ = lean_ctor_get(v_e_1287_, 1);
v___x_1291_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_expr_1290_, v_newExpr_1288_);
if (v___x_1291_ == 0)
{
lean_object* v___x_1292_; 
lean_inc(v_data_1289_);
lean_dec_ref(v_e_1287_);
v___x_1292_ = l_Lean_Meta_Sym_Internal_mkMDataS___redArg(v_inst_1285_, v_inst_1286_, v_data_1289_, v_newExpr_1288_);
return v___x_1292_;
}
else
{
lean_object* v_toApplicative_1293_; lean_object* v_toPure_1294_; lean_object* v___x_1295_; 
lean_dec_ref(v_newExpr_1288_);
lean_dec_ref(v_inst_1285_);
v_toApplicative_1293_ = lean_ctor_get(v_inst_1286_, 0);
lean_inc_ref(v_toApplicative_1293_);
lean_dec_ref(v_inst_1286_);
v_toPure_1294_ = lean_ctor_get(v_toApplicative_1293_, 1);
lean_inc(v_toPure_1294_);
lean_dec_ref(v_toApplicative_1293_);
v___x_1295_ = lean_apply_2(v_toPure_1294_, lean_box(0), v_e_1287_);
return v___x_1295_;
}
}
else
{
lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; 
lean_dec_ref(v_newExpr_1288_);
lean_dec_ref(v_e_1287_);
lean_dec_ref(v_inst_1285_);
v___x_1296_ = l_Lean_instInhabitedExpr;
v___x_1297_ = l_instInhabitedOfMonad___redArg(v_inst_1286_, v___x_1296_);
v___x_1298_ = lean_obj_once(&l_Lean_Expr_updateMDataS_x21___redArg___closed__2, &l_Lean_Expr_updateMDataS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateMDataS_x21___redArg___closed__2);
v___x_1299_ = l_panic___redArg(v___x_1297_, v___x_1298_);
lean_dec(v___x_1297_);
return v___x_1299_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateMDataS_x21(lean_object* v_m_1300_, lean_object* v_inst_1301_, lean_object* v_inst_1302_, lean_object* v_e_1303_, lean_object* v_newExpr_1304_){
_start:
{
if (lean_obj_tag(v_e_1303_) == 10)
{
lean_object* v_data_1305_; lean_object* v_expr_1306_; uint8_t v___x_1307_; 
v_data_1305_ = lean_ctor_get(v_e_1303_, 0);
v_expr_1306_ = lean_ctor_get(v_e_1303_, 1);
v___x_1307_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_expr_1306_, v_newExpr_1304_);
if (v___x_1307_ == 0)
{
lean_object* v___x_1308_; 
lean_inc(v_data_1305_);
lean_dec_ref(v_e_1303_);
v___x_1308_ = l_Lean_Meta_Sym_Internal_mkMDataS___redArg(v_inst_1301_, v_inst_1302_, v_data_1305_, v_newExpr_1304_);
return v___x_1308_;
}
else
{
lean_object* v_toApplicative_1309_; lean_object* v_toPure_1310_; lean_object* v___x_1311_; 
lean_dec_ref(v_newExpr_1304_);
lean_dec_ref(v_inst_1301_);
v_toApplicative_1309_ = lean_ctor_get(v_inst_1302_, 0);
lean_inc_ref(v_toApplicative_1309_);
lean_dec_ref(v_inst_1302_);
v_toPure_1310_ = lean_ctor_get(v_toApplicative_1309_, 1);
lean_inc(v_toPure_1310_);
lean_dec_ref(v_toApplicative_1309_);
v___x_1311_ = lean_apply_2(v_toPure_1310_, lean_box(0), v_e_1303_);
return v___x_1311_;
}
}
else
{
lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; 
lean_dec_ref(v_newExpr_1304_);
lean_dec_ref(v_e_1303_);
lean_dec_ref(v_inst_1301_);
v___x_1312_ = l_Lean_instInhabitedExpr;
v___x_1313_ = l_instInhabitedOfMonad___redArg(v_inst_1302_, v___x_1312_);
v___x_1314_ = lean_obj_once(&l_Lean_Expr_updateMDataS_x21___redArg___closed__2, &l_Lean_Expr_updateMDataS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateMDataS_x21___redArg___closed__2);
v___x_1315_ = l_panic___redArg(v___x_1313_, v___x_1314_);
lean_dec(v___x_1313_);
return v___x_1315_;
}
}
}
static lean_object* _init_l_Lean_Expr_updateProjS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; 
v___x_1318_ = ((lean_object*)(l_Lean_Expr_updateProjS_x21___redArg___closed__1));
v___x_1319_ = lean_unsigned_to_nat(25u);
v___x_1320_ = lean_unsigned_to_nat(156u);
v___x_1321_ = ((lean_object*)(l_Lean_Expr_updateProjS_x21___redArg___closed__0));
v___x_1322_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1323_ = l_mkPanicMessageWithDecl(v___x_1322_, v___x_1321_, v___x_1320_, v___x_1319_, v___x_1318_);
return v___x_1323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateProjS_x21___redArg(lean_object* v_inst_1324_, lean_object* v_inst_1325_, lean_object* v_e_1326_, lean_object* v_newExpr_1327_){
_start:
{
if (lean_obj_tag(v_e_1326_) == 11)
{
lean_object* v_typeName_1328_; lean_object* v_idx_1329_; lean_object* v_struct_1330_; uint8_t v___x_1331_; 
v_typeName_1328_ = lean_ctor_get(v_e_1326_, 0);
v_idx_1329_ = lean_ctor_get(v_e_1326_, 1);
v_struct_1330_ = lean_ctor_get(v_e_1326_, 2);
v___x_1331_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_1330_, v_newExpr_1327_);
if (v___x_1331_ == 0)
{
lean_object* v___x_1332_; 
lean_inc(v_idx_1329_);
lean_inc(v_typeName_1328_);
lean_dec_ref(v_e_1326_);
v___x_1332_ = l_Lean_Meta_Sym_Internal_mkProjS___redArg(v_inst_1324_, v_inst_1325_, v_typeName_1328_, v_idx_1329_, v_newExpr_1327_);
return v___x_1332_;
}
else
{
lean_object* v_toApplicative_1333_; lean_object* v_toPure_1334_; lean_object* v___x_1335_; 
lean_dec_ref(v_newExpr_1327_);
lean_dec_ref(v_inst_1324_);
v_toApplicative_1333_ = lean_ctor_get(v_inst_1325_, 0);
lean_inc_ref(v_toApplicative_1333_);
lean_dec_ref(v_inst_1325_);
v_toPure_1334_ = lean_ctor_get(v_toApplicative_1333_, 1);
lean_inc(v_toPure_1334_);
lean_dec_ref(v_toApplicative_1333_);
v___x_1335_ = lean_apply_2(v_toPure_1334_, lean_box(0), v_e_1326_);
return v___x_1335_;
}
}
else
{
lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; 
lean_dec_ref(v_newExpr_1327_);
lean_dec_ref(v_e_1326_);
lean_dec_ref(v_inst_1324_);
v___x_1336_ = l_Lean_instInhabitedExpr;
v___x_1337_ = l_instInhabitedOfMonad___redArg(v_inst_1325_, v___x_1336_);
v___x_1338_ = lean_obj_once(&l_Lean_Expr_updateProjS_x21___redArg___closed__2, &l_Lean_Expr_updateProjS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateProjS_x21___redArg___closed__2);
v___x_1339_ = l_panic___redArg(v___x_1337_, v___x_1338_);
lean_dec(v___x_1337_);
return v___x_1339_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateProjS_x21(lean_object* v_m_1340_, lean_object* v_inst_1341_, lean_object* v_inst_1342_, lean_object* v_e_1343_, lean_object* v_newExpr_1344_){
_start:
{
if (lean_obj_tag(v_e_1343_) == 11)
{
lean_object* v_typeName_1345_; lean_object* v_idx_1346_; lean_object* v_struct_1347_; uint8_t v___x_1348_; 
v_typeName_1345_ = lean_ctor_get(v_e_1343_, 0);
v_idx_1346_ = lean_ctor_get(v_e_1343_, 1);
v_struct_1347_ = lean_ctor_get(v_e_1343_, 2);
v___x_1348_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_1347_, v_newExpr_1344_);
if (v___x_1348_ == 0)
{
lean_object* v___x_1349_; 
lean_inc(v_idx_1346_);
lean_inc(v_typeName_1345_);
lean_dec_ref(v_e_1343_);
v___x_1349_ = l_Lean_Meta_Sym_Internal_mkProjS___redArg(v_inst_1341_, v_inst_1342_, v_typeName_1345_, v_idx_1346_, v_newExpr_1344_);
return v___x_1349_;
}
else
{
lean_object* v_toApplicative_1350_; lean_object* v_toPure_1351_; lean_object* v___x_1352_; 
lean_dec_ref(v_newExpr_1344_);
lean_dec_ref(v_inst_1341_);
v_toApplicative_1350_ = lean_ctor_get(v_inst_1342_, 0);
lean_inc_ref(v_toApplicative_1350_);
lean_dec_ref(v_inst_1342_);
v_toPure_1351_ = lean_ctor_get(v_toApplicative_1350_, 1);
lean_inc(v_toPure_1351_);
lean_dec_ref(v_toApplicative_1350_);
v___x_1352_ = lean_apply_2(v_toPure_1351_, lean_box(0), v_e_1343_);
return v___x_1352_;
}
}
else
{
lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; 
lean_dec_ref(v_newExpr_1344_);
lean_dec_ref(v_e_1343_);
lean_dec_ref(v_inst_1341_);
v___x_1353_ = l_Lean_instInhabitedExpr;
v___x_1354_ = l_instInhabitedOfMonad___redArg(v_inst_1342_, v___x_1353_);
v___x_1355_ = lean_obj_once(&l_Lean_Expr_updateProjS_x21___redArg___closed__2, &l_Lean_Expr_updateProjS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateProjS_x21___redArg___closed__2);
v___x_1356_ = l_panic___redArg(v___x_1354_, v___x_1355_);
lean_dec(v___x_1354_);
return v___x_1356_;
}
}
}
static lean_object* _init_l_Lean_Expr_updateForallS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; 
v___x_1359_ = ((lean_object*)(l_Lean_Expr_updateForallS_x21___redArg___closed__1));
v___x_1360_ = lean_unsigned_to_nat(31u);
v___x_1361_ = lean_unsigned_to_nat(160u);
v___x_1362_ = ((lean_object*)(l_Lean_Expr_updateForallS_x21___redArg___closed__0));
v___x_1363_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1364_ = l_mkPanicMessageWithDecl(v___x_1363_, v___x_1362_, v___x_1361_, v___x_1360_, v___x_1359_);
return v___x_1364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallS_x21___redArg(lean_object* v_inst_1365_, lean_object* v_inst_1366_, lean_object* v_e_1367_, lean_object* v_newDomain_1368_, lean_object* v_newBody_1369_){
_start:
{
if (lean_obj_tag(v_e_1367_) == 7)
{
lean_object* v_binderName_1370_; lean_object* v_binderType_1371_; lean_object* v_body_1372_; uint8_t v_binderInfo_1373_; uint8_t v___y_1375_; uint8_t v___x_1380_; 
v_binderName_1370_ = lean_ctor_get(v_e_1367_, 0);
v_binderType_1371_ = lean_ctor_get(v_e_1367_, 1);
v_body_1372_ = lean_ctor_get(v_e_1367_, 2);
v_binderInfo_1373_ = lean_ctor_get_uint8(v_e_1367_, sizeof(void*)*3 + 8);
v___x_1380_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_1371_, v_newDomain_1368_);
if (v___x_1380_ == 0)
{
v___y_1375_ = v___x_1380_;
goto v___jp_1374_;
}
else
{
uint8_t v___x_1381_; 
v___x_1381_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1372_, v_newBody_1369_);
v___y_1375_ = v___x_1381_;
goto v___jp_1374_;
}
v___jp_1374_:
{
if (v___y_1375_ == 0)
{
lean_object* v___x_1376_; 
lean_inc(v_binderName_1370_);
lean_dec_ref(v_e_1367_);
v___x_1376_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v_inst_1365_, v_inst_1366_, v_binderName_1370_, v_binderInfo_1373_, v_newDomain_1368_, v_newBody_1369_);
return v___x_1376_;
}
else
{
lean_object* v_toApplicative_1377_; lean_object* v_toPure_1378_; lean_object* v___x_1379_; 
lean_dec_ref(v_newBody_1369_);
lean_dec_ref(v_newDomain_1368_);
lean_dec_ref(v_inst_1365_);
v_toApplicative_1377_ = lean_ctor_get(v_inst_1366_, 0);
lean_inc_ref(v_toApplicative_1377_);
lean_dec_ref(v_inst_1366_);
v_toPure_1378_ = lean_ctor_get(v_toApplicative_1377_, 1);
lean_inc(v_toPure_1378_);
lean_dec_ref(v_toApplicative_1377_);
v___x_1379_ = lean_apply_2(v_toPure_1378_, lean_box(0), v_e_1367_);
return v___x_1379_;
}
}
}
else
{
lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; 
lean_dec_ref(v_newBody_1369_);
lean_dec_ref(v_newDomain_1368_);
lean_dec_ref(v_e_1367_);
lean_dec_ref(v_inst_1365_);
v___x_1382_ = l_Lean_instInhabitedExpr;
v___x_1383_ = l_instInhabitedOfMonad___redArg(v_inst_1366_, v___x_1382_);
v___x_1384_ = lean_obj_once(&l_Lean_Expr_updateForallS_x21___redArg___closed__2, &l_Lean_Expr_updateForallS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateForallS_x21___redArg___closed__2);
v___x_1385_ = l_panic___redArg(v___x_1383_, v___x_1384_);
lean_dec(v___x_1383_);
return v___x_1385_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallS_x21(lean_object* v_m_1386_, lean_object* v_inst_1387_, lean_object* v_inst_1388_, lean_object* v_e_1389_, lean_object* v_newDomain_1390_, lean_object* v_newBody_1391_){
_start:
{
if (lean_obj_tag(v_e_1389_) == 7)
{
lean_object* v_binderName_1392_; lean_object* v_binderType_1393_; lean_object* v_body_1394_; uint8_t v_binderInfo_1395_; uint8_t v___y_1397_; uint8_t v___x_1402_; 
v_binderName_1392_ = lean_ctor_get(v_e_1389_, 0);
v_binderType_1393_ = lean_ctor_get(v_e_1389_, 1);
v_body_1394_ = lean_ctor_get(v_e_1389_, 2);
v_binderInfo_1395_ = lean_ctor_get_uint8(v_e_1389_, sizeof(void*)*3 + 8);
v___x_1402_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_1393_, v_newDomain_1390_);
if (v___x_1402_ == 0)
{
v___y_1397_ = v___x_1402_;
goto v___jp_1396_;
}
else
{
uint8_t v___x_1403_; 
v___x_1403_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1394_, v_newBody_1391_);
v___y_1397_ = v___x_1403_;
goto v___jp_1396_;
}
v___jp_1396_:
{
if (v___y_1397_ == 0)
{
lean_object* v___x_1398_; 
lean_inc(v_binderName_1392_);
lean_dec_ref(v_e_1389_);
v___x_1398_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v_inst_1387_, v_inst_1388_, v_binderName_1392_, v_binderInfo_1395_, v_newDomain_1390_, v_newBody_1391_);
return v___x_1398_;
}
else
{
lean_object* v_toApplicative_1399_; lean_object* v_toPure_1400_; lean_object* v___x_1401_; 
lean_dec_ref(v_newBody_1391_);
lean_dec_ref(v_newDomain_1390_);
lean_dec_ref(v_inst_1387_);
v_toApplicative_1399_ = lean_ctor_get(v_inst_1388_, 0);
lean_inc_ref(v_toApplicative_1399_);
lean_dec_ref(v_inst_1388_);
v_toPure_1400_ = lean_ctor_get(v_toApplicative_1399_, 1);
lean_inc(v_toPure_1400_);
lean_dec_ref(v_toApplicative_1399_);
v___x_1401_ = lean_apply_2(v_toPure_1400_, lean_box(0), v_e_1389_);
return v___x_1401_;
}
}
}
else
{
lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; 
lean_dec_ref(v_newBody_1391_);
lean_dec_ref(v_newDomain_1390_);
lean_dec_ref(v_e_1389_);
lean_dec_ref(v_inst_1387_);
v___x_1404_ = l_Lean_instInhabitedExpr;
v___x_1405_ = l_instInhabitedOfMonad___redArg(v_inst_1388_, v___x_1404_);
v___x_1406_ = lean_obj_once(&l_Lean_Expr_updateForallS_x21___redArg___closed__2, &l_Lean_Expr_updateForallS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateForallS_x21___redArg___closed__2);
v___x_1407_ = l_panic___redArg(v___x_1405_, v___x_1406_);
lean_dec(v___x_1405_);
return v___x_1407_;
}
}
}
static lean_object* _init_l_Lean_Expr_updateLambdaS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1410_ = ((lean_object*)(l_Lean_Expr_updateLambdaS_x21___redArg___closed__1));
v___x_1411_ = lean_unsigned_to_nat(27u);
v___x_1412_ = lean_unsigned_to_nat(167u);
v___x_1413_ = ((lean_object*)(l_Lean_Expr_updateLambdaS_x21___redArg___closed__0));
v___x_1414_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1415_ = l_mkPanicMessageWithDecl(v___x_1414_, v___x_1413_, v___x_1412_, v___x_1411_, v___x_1410_);
return v___x_1415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLambdaS_x21___redArg(lean_object* v_inst_1416_, lean_object* v_inst_1417_, lean_object* v_e_1418_, lean_object* v_newDomain_1419_, lean_object* v_newBody_1420_){
_start:
{
if (lean_obj_tag(v_e_1418_) == 6)
{
lean_object* v_binderName_1421_; lean_object* v_binderType_1422_; lean_object* v_body_1423_; uint8_t v_binderInfo_1424_; uint8_t v___y_1426_; uint8_t v___x_1431_; 
v_binderName_1421_ = lean_ctor_get(v_e_1418_, 0);
v_binderType_1422_ = lean_ctor_get(v_e_1418_, 1);
v_body_1423_ = lean_ctor_get(v_e_1418_, 2);
v_binderInfo_1424_ = lean_ctor_get_uint8(v_e_1418_, sizeof(void*)*3 + 8);
v___x_1431_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_1422_, v_newDomain_1419_);
if (v___x_1431_ == 0)
{
v___y_1426_ = v___x_1431_;
goto v___jp_1425_;
}
else
{
uint8_t v___x_1432_; 
v___x_1432_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1423_, v_newBody_1420_);
v___y_1426_ = v___x_1432_;
goto v___jp_1425_;
}
v___jp_1425_:
{
if (v___y_1426_ == 0)
{
lean_object* v___x_1427_; 
lean_inc(v_binderName_1421_);
lean_dec_ref(v_e_1418_);
v___x_1427_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v_inst_1416_, v_inst_1417_, v_binderName_1421_, v_binderInfo_1424_, v_newDomain_1419_, v_newBody_1420_);
return v___x_1427_;
}
else
{
lean_object* v_toApplicative_1428_; lean_object* v_toPure_1429_; lean_object* v___x_1430_; 
lean_dec_ref(v_newBody_1420_);
lean_dec_ref(v_newDomain_1419_);
lean_dec_ref(v_inst_1416_);
v_toApplicative_1428_ = lean_ctor_get(v_inst_1417_, 0);
lean_inc_ref(v_toApplicative_1428_);
lean_dec_ref(v_inst_1417_);
v_toPure_1429_ = lean_ctor_get(v_toApplicative_1428_, 1);
lean_inc(v_toPure_1429_);
lean_dec_ref(v_toApplicative_1428_);
v___x_1430_ = lean_apply_2(v_toPure_1429_, lean_box(0), v_e_1418_);
return v___x_1430_;
}
}
}
else
{
lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; 
lean_dec_ref(v_newBody_1420_);
lean_dec_ref(v_newDomain_1419_);
lean_dec_ref(v_e_1418_);
lean_dec_ref(v_inst_1416_);
v___x_1433_ = l_Lean_instInhabitedExpr;
v___x_1434_ = l_instInhabitedOfMonad___redArg(v_inst_1417_, v___x_1433_);
v___x_1435_ = lean_obj_once(&l_Lean_Expr_updateLambdaS_x21___redArg___closed__2, &l_Lean_Expr_updateLambdaS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateLambdaS_x21___redArg___closed__2);
v___x_1436_ = l_panic___redArg(v___x_1434_, v___x_1435_);
lean_dec(v___x_1434_);
return v___x_1436_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLambdaS_x21(lean_object* v_m_1437_, lean_object* v_inst_1438_, lean_object* v_inst_1439_, lean_object* v_e_1440_, lean_object* v_newDomain_1441_, lean_object* v_newBody_1442_){
_start:
{
if (lean_obj_tag(v_e_1440_) == 6)
{
lean_object* v_binderName_1443_; lean_object* v_binderType_1444_; lean_object* v_body_1445_; uint8_t v_binderInfo_1446_; uint8_t v___y_1448_; uint8_t v___x_1453_; 
v_binderName_1443_ = lean_ctor_get(v_e_1440_, 0);
v_binderType_1444_ = lean_ctor_get(v_e_1440_, 1);
v_body_1445_ = lean_ctor_get(v_e_1440_, 2);
v_binderInfo_1446_ = lean_ctor_get_uint8(v_e_1440_, sizeof(void*)*3 + 8);
v___x_1453_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_1444_, v_newDomain_1441_);
if (v___x_1453_ == 0)
{
v___y_1448_ = v___x_1453_;
goto v___jp_1447_;
}
else
{
uint8_t v___x_1454_; 
v___x_1454_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1445_, v_newBody_1442_);
v___y_1448_ = v___x_1454_;
goto v___jp_1447_;
}
v___jp_1447_:
{
if (v___y_1448_ == 0)
{
lean_object* v___x_1449_; 
lean_inc(v_binderName_1443_);
lean_dec_ref(v_e_1440_);
v___x_1449_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v_inst_1438_, v_inst_1439_, v_binderName_1443_, v_binderInfo_1446_, v_newDomain_1441_, v_newBody_1442_);
return v___x_1449_;
}
else
{
lean_object* v_toApplicative_1450_; lean_object* v_toPure_1451_; lean_object* v___x_1452_; 
lean_dec_ref(v_newBody_1442_);
lean_dec_ref(v_newDomain_1441_);
lean_dec_ref(v_inst_1438_);
v_toApplicative_1450_ = lean_ctor_get(v_inst_1439_, 0);
lean_inc_ref(v_toApplicative_1450_);
lean_dec_ref(v_inst_1439_);
v_toPure_1451_ = lean_ctor_get(v_toApplicative_1450_, 1);
lean_inc(v_toPure_1451_);
lean_dec_ref(v_toApplicative_1450_);
v___x_1452_ = lean_apply_2(v_toPure_1451_, lean_box(0), v_e_1440_);
return v___x_1452_;
}
}
}
else
{
lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; 
lean_dec_ref(v_newBody_1442_);
lean_dec_ref(v_newDomain_1441_);
lean_dec_ref(v_e_1440_);
lean_dec_ref(v_inst_1438_);
v___x_1455_ = l_Lean_instInhabitedExpr;
v___x_1456_ = l_instInhabitedOfMonad___redArg(v_inst_1439_, v___x_1455_);
v___x_1457_ = lean_obj_once(&l_Lean_Expr_updateLambdaS_x21___redArg___closed__2, &l_Lean_Expr_updateLambdaS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateLambdaS_x21___redArg___closed__2);
v___x_1458_ = l_panic___redArg(v___x_1456_, v___x_1457_);
lean_dec(v___x_1456_);
return v___x_1458_;
}
}
}
static lean_object* _init_l_Lean_Expr_updateLetS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; 
v___x_1461_ = ((lean_object*)(l_Lean_Expr_updateLetS_x21___redArg___closed__1));
v___x_1462_ = lean_unsigned_to_nat(34u);
v___x_1463_ = lean_unsigned_to_nat(174u);
v___x_1464_ = ((lean_object*)(l_Lean_Expr_updateLetS_x21___redArg___closed__0));
v___x_1465_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1466_ = l_mkPanicMessageWithDecl(v___x_1465_, v___x_1464_, v___x_1463_, v___x_1462_, v___x_1461_);
return v___x_1466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLetS_x21___redArg(lean_object* v_inst_1467_, lean_object* v_inst_1468_, lean_object* v_e_1469_, lean_object* v_newType_1470_, lean_object* v_newVal_1471_, lean_object* v_newBody_1472_){
_start:
{
if (lean_obj_tag(v_e_1469_) == 8)
{
lean_object* v_declName_1473_; lean_object* v_type_1474_; lean_object* v_value_1475_; lean_object* v_body_1476_; uint8_t v_nondep_1477_; uint8_t v___y_1479_; uint8_t v___x_1486_; 
v_declName_1473_ = lean_ctor_get(v_e_1469_, 0);
v_type_1474_ = lean_ctor_get(v_e_1469_, 1);
v_value_1475_ = lean_ctor_get(v_e_1469_, 2);
v_body_1476_ = lean_ctor_get(v_e_1469_, 3);
v_nondep_1477_ = lean_ctor_get_uint8(v_e_1469_, sizeof(void*)*4 + 8);
v___x_1486_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_type_1474_, v_newType_1470_);
if (v___x_1486_ == 0)
{
v___y_1479_ = v___x_1486_;
goto v___jp_1478_;
}
else
{
uint8_t v___x_1487_; 
v___x_1487_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_value_1475_, v_newVal_1471_);
v___y_1479_ = v___x_1487_;
goto v___jp_1478_;
}
v___jp_1478_:
{
if (v___y_1479_ == 0)
{
lean_object* v___x_1480_; 
lean_inc(v_declName_1473_);
lean_dec_ref(v_e_1469_);
v___x_1480_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1467_, v_inst_1468_, v_declName_1473_, v_newType_1470_, v_newVal_1471_, v_newBody_1472_, v_nondep_1477_);
return v___x_1480_;
}
else
{
uint8_t v___x_1481_; 
v___x_1481_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1476_, v_newBody_1472_);
if (v___x_1481_ == 0)
{
lean_object* v___x_1482_; 
lean_inc(v_declName_1473_);
lean_dec_ref(v_e_1469_);
v___x_1482_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1467_, v_inst_1468_, v_declName_1473_, v_newType_1470_, v_newVal_1471_, v_newBody_1472_, v_nondep_1477_);
return v___x_1482_;
}
else
{
lean_object* v_toApplicative_1483_; lean_object* v_toPure_1484_; lean_object* v___x_1485_; 
lean_dec_ref(v_newBody_1472_);
lean_dec_ref(v_newVal_1471_);
lean_dec_ref(v_newType_1470_);
lean_dec_ref(v_inst_1467_);
v_toApplicative_1483_ = lean_ctor_get(v_inst_1468_, 0);
lean_inc_ref(v_toApplicative_1483_);
lean_dec_ref(v_inst_1468_);
v_toPure_1484_ = lean_ctor_get(v_toApplicative_1483_, 1);
lean_inc(v_toPure_1484_);
lean_dec_ref(v_toApplicative_1483_);
v___x_1485_ = lean_apply_2(v_toPure_1484_, lean_box(0), v_e_1469_);
return v___x_1485_;
}
}
}
}
else
{
lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; 
lean_dec_ref(v_newBody_1472_);
lean_dec_ref(v_newVal_1471_);
lean_dec_ref(v_newType_1470_);
lean_dec_ref(v_e_1469_);
lean_dec_ref(v_inst_1467_);
v___x_1488_ = l_Lean_instInhabitedExpr;
v___x_1489_ = l_instInhabitedOfMonad___redArg(v_inst_1468_, v___x_1488_);
v___x_1490_ = lean_obj_once(&l_Lean_Expr_updateLetS_x21___redArg___closed__2, &l_Lean_Expr_updateLetS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateLetS_x21___redArg___closed__2);
v___x_1491_ = l_panic___redArg(v___x_1489_, v___x_1490_);
lean_dec(v___x_1489_);
return v___x_1491_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLetS_x21(lean_object* v_m_1492_, lean_object* v_inst_1493_, lean_object* v_inst_1494_, lean_object* v_e_1495_, lean_object* v_newType_1496_, lean_object* v_newVal_1497_, lean_object* v_newBody_1498_){
_start:
{
if (lean_obj_tag(v_e_1495_) == 8)
{
lean_object* v_declName_1499_; lean_object* v_type_1500_; lean_object* v_value_1501_; lean_object* v_body_1502_; uint8_t v_nondep_1503_; uint8_t v___y_1505_; uint8_t v___x_1512_; 
v_declName_1499_ = lean_ctor_get(v_e_1495_, 0);
v_type_1500_ = lean_ctor_get(v_e_1495_, 1);
v_value_1501_ = lean_ctor_get(v_e_1495_, 2);
v_body_1502_ = lean_ctor_get(v_e_1495_, 3);
v_nondep_1503_ = lean_ctor_get_uint8(v_e_1495_, sizeof(void*)*4 + 8);
v___x_1512_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_type_1500_, v_newType_1496_);
if (v___x_1512_ == 0)
{
v___y_1505_ = v___x_1512_;
goto v___jp_1504_;
}
else
{
uint8_t v___x_1513_; 
v___x_1513_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_value_1501_, v_newVal_1497_);
v___y_1505_ = v___x_1513_;
goto v___jp_1504_;
}
v___jp_1504_:
{
if (v___y_1505_ == 0)
{
lean_object* v___x_1506_; 
lean_inc(v_declName_1499_);
lean_dec_ref(v_e_1495_);
v___x_1506_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1493_, v_inst_1494_, v_declName_1499_, v_newType_1496_, v_newVal_1497_, v_newBody_1498_, v_nondep_1503_);
return v___x_1506_;
}
else
{
uint8_t v___x_1507_; 
v___x_1507_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1502_, v_newBody_1498_);
if (v___x_1507_ == 0)
{
lean_object* v___x_1508_; 
lean_inc(v_declName_1499_);
lean_dec_ref(v_e_1495_);
v___x_1508_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1493_, v_inst_1494_, v_declName_1499_, v_newType_1496_, v_newVal_1497_, v_newBody_1498_, v_nondep_1503_);
return v___x_1508_;
}
else
{
lean_object* v_toApplicative_1509_; lean_object* v_toPure_1510_; lean_object* v___x_1511_; 
lean_dec_ref(v_newBody_1498_);
lean_dec_ref(v_newVal_1497_);
lean_dec_ref(v_newType_1496_);
lean_dec_ref(v_inst_1493_);
v_toApplicative_1509_ = lean_ctor_get(v_inst_1494_, 0);
lean_inc_ref(v_toApplicative_1509_);
lean_dec_ref(v_inst_1494_);
v_toPure_1510_ = lean_ctor_get(v_toApplicative_1509_, 1);
lean_inc(v_toPure_1510_);
lean_dec_ref(v_toApplicative_1509_);
v___x_1511_ = lean_apply_2(v_toPure_1510_, lean_box(0), v_e_1495_);
return v___x_1511_;
}
}
}
}
else
{
lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; 
lean_dec_ref(v_newBody_1498_);
lean_dec_ref(v_newVal_1497_);
lean_dec_ref(v_newType_1496_);
lean_dec_ref(v_e_1495_);
lean_dec_ref(v_inst_1493_);
v___x_1514_ = l_Lean_instInhabitedExpr;
v___x_1515_ = l_instInhabitedOfMonad___redArg(v_inst_1494_, v___x_1514_);
v___x_1516_ = lean_obj_once(&l_Lean_Expr_updateLetS_x21___redArg___closed__2, &l_Lean_Expr_updateLetS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateLetS_x21___redArg___closed__2);
v___x_1517_ = l_panic___redArg(v___x_1515_, v___x_1516_);
lean_dec(v___x_1515_);
return v___x_1517_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___redArg___lam__0(lean_object* v_inst_1518_, lean_object* v_inst_1519_, lean_object* v_a_u2082_1520_, lean_object* v_____do__lift_1521_){
_start:
{
lean_object* v___x_1522_; 
v___x_1522_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1518_, v_inst_1519_, v_____do__lift_1521_, v_a_u2082_1520_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___redArg(lean_object* v_inst_1523_, lean_object* v_inst_1524_, lean_object* v_f_1525_, lean_object* v_a_u2081_1526_, lean_object* v_a_u2082_1527_){
_start:
{
lean_object* v_toBind_1528_; lean_object* v___f_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; 
v_toBind_1528_ = lean_ctor_get(v_inst_1524_, 1);
lean_inc(v_toBind_1528_);
lean_inc_ref(v_inst_1524_);
lean_inc_ref(v_inst_1523_);
v___f_1529_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2082___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1529_, 0, v_inst_1523_);
lean_closure_set(v___f_1529_, 1, v_inst_1524_);
lean_closure_set(v___f_1529_, 2, v_a_u2082_1527_);
v___x_1530_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1523_, v_inst_1524_, v_f_1525_, v_a_u2081_1526_);
v___x_1531_ = lean_apply_4(v_toBind_1528_, lean_box(0), lean_box(0), v___x_1530_, v___f_1529_);
return v___x_1531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082(lean_object* v_m_1532_, lean_object* v_inst_1533_, lean_object* v_inst_1534_, lean_object* v_f_1535_, lean_object* v_a_u2081_1536_, lean_object* v_a_u2082_1537_){
_start:
{
lean_object* v___x_1538_; 
v___x_1538_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___redArg(v_inst_1533_, v_inst_1534_, v_f_1535_, v_a_u2081_1536_, v_a_u2082_1537_);
return v___x_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___redArg___lam__0(lean_object* v_inst_1539_, lean_object* v_inst_1540_, lean_object* v_a_u2083_1541_, lean_object* v_____do__lift_1542_){
_start:
{
lean_object* v___x_1543_; 
v___x_1543_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1539_, v_inst_1540_, v_____do__lift_1542_, v_a_u2083_1541_);
return v___x_1543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___redArg(lean_object* v_inst_1544_, lean_object* v_inst_1545_, lean_object* v_f_1546_, lean_object* v_a_u2081_1547_, lean_object* v_a_u2082_1548_, lean_object* v_a_u2083_1549_){
_start:
{
lean_object* v_toBind_1550_; lean_object* v___f_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; 
v_toBind_1550_ = lean_ctor_get(v_inst_1545_, 1);
lean_inc(v_toBind_1550_);
lean_inc_ref(v_inst_1545_);
lean_inc_ref(v_inst_1544_);
v___f_1551_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2083___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1551_, 0, v_inst_1544_);
lean_closure_set(v___f_1551_, 1, v_inst_1545_);
lean_closure_set(v___f_1551_, 2, v_a_u2083_1549_);
v___x_1552_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___redArg(v_inst_1544_, v_inst_1545_, v_f_1546_, v_a_u2081_1547_, v_a_u2082_1548_);
v___x_1553_ = lean_apply_4(v_toBind_1550_, lean_box(0), lean_box(0), v___x_1552_, v___f_1551_);
return v___x_1553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083(lean_object* v_m_1554_, lean_object* v_inst_1555_, lean_object* v_inst_1556_, lean_object* v_f_1557_, lean_object* v_a_u2081_1558_, lean_object* v_a_u2082_1559_, lean_object* v_a_u2083_1560_){
_start:
{
lean_object* v___x_1561_; 
v___x_1561_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___redArg(v_inst_1555_, v_inst_1556_, v_f_1557_, v_a_u2081_1558_, v_a_u2082_1559_, v_a_u2083_1560_);
return v___x_1561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___redArg___lam__0(lean_object* v_inst_1562_, lean_object* v_inst_1563_, lean_object* v_a_u2084_1564_, lean_object* v_____do__lift_1565_){
_start:
{
lean_object* v___x_1566_; 
v___x_1566_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1562_, v_inst_1563_, v_____do__lift_1565_, v_a_u2084_1564_);
return v___x_1566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___redArg(lean_object* v_inst_1567_, lean_object* v_inst_1568_, lean_object* v_f_1569_, lean_object* v_a_u2081_1570_, lean_object* v_a_u2082_1571_, lean_object* v_a_u2083_1572_, lean_object* v_a_u2084_1573_){
_start:
{
lean_object* v_toBind_1574_; lean_object* v___f_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; 
v_toBind_1574_ = lean_ctor_get(v_inst_1568_, 1);
lean_inc(v_toBind_1574_);
lean_inc_ref(v_inst_1568_);
lean_inc_ref(v_inst_1567_);
v___f_1575_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2084___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1575_, 0, v_inst_1567_);
lean_closure_set(v___f_1575_, 1, v_inst_1568_);
lean_closure_set(v___f_1575_, 2, v_a_u2084_1573_);
v___x_1576_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___redArg(v_inst_1567_, v_inst_1568_, v_f_1569_, v_a_u2081_1570_, v_a_u2082_1571_, v_a_u2083_1572_);
v___x_1577_ = lean_apply_4(v_toBind_1574_, lean_box(0), lean_box(0), v___x_1576_, v___f_1575_);
return v___x_1577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084(lean_object* v_m_1578_, lean_object* v_inst_1579_, lean_object* v_inst_1580_, lean_object* v_f_1581_, lean_object* v_a_u2081_1582_, lean_object* v_a_u2082_1583_, lean_object* v_a_u2083_1584_, lean_object* v_a_u2084_1585_){
_start:
{
lean_object* v___x_1586_; 
v___x_1586_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___redArg(v_inst_1579_, v_inst_1580_, v_f_1581_, v_a_u2081_1582_, v_a_u2082_1583_, v_a_u2083_1584_, v_a_u2084_1585_);
return v___x_1586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2085___redArg___lam__0(lean_object* v_inst_1587_, lean_object* v_inst_1588_, lean_object* v_a_u2085_1589_, lean_object* v_____do__lift_1590_){
_start:
{
lean_object* v___x_1591_; 
v___x_1591_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1587_, v_inst_1588_, v_____do__lift_1590_, v_a_u2085_1589_);
return v___x_1591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2085___redArg(lean_object* v_inst_1592_, lean_object* v_inst_1593_, lean_object* v_f_1594_, lean_object* v_a_u2081_1595_, lean_object* v_a_u2082_1596_, lean_object* v_a_u2083_1597_, lean_object* v_a_u2084_1598_, lean_object* v_a_u2085_1599_){
_start:
{
lean_object* v_toBind_1600_; lean_object* v___f_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; 
v_toBind_1600_ = lean_ctor_get(v_inst_1593_, 1);
lean_inc(v_toBind_1600_);
lean_inc_ref(v_inst_1593_);
lean_inc_ref(v_inst_1592_);
v___f_1601_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2085___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1601_, 0, v_inst_1592_);
lean_closure_set(v___f_1601_, 1, v_inst_1593_);
lean_closure_set(v___f_1601_, 2, v_a_u2085_1599_);
v___x_1602_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___redArg(v_inst_1592_, v_inst_1593_, v_f_1594_, v_a_u2081_1595_, v_a_u2082_1596_, v_a_u2083_1597_, v_a_u2084_1598_);
v___x_1603_ = lean_apply_4(v_toBind_1600_, lean_box(0), lean_box(0), v___x_1602_, v___f_1601_);
return v___x_1603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2085(lean_object* v_m_1604_, lean_object* v_inst_1605_, lean_object* v_inst_1606_, lean_object* v_f_1607_, lean_object* v_a_u2081_1608_, lean_object* v_a_u2082_1609_, lean_object* v_a_u2083_1610_, lean_object* v_a_u2084_1611_, lean_object* v_a_u2085_1612_){
_start:
{
lean_object* v___x_1613_; 
v___x_1613_ = l_Lean_Meta_Sym_Internal_mkAppS_u2085___redArg(v_inst_1605_, v_inst_1606_, v_f_1607_, v_a_u2081_1608_, v_a_u2082_1609_, v_a_u2083_1610_, v_a_u2084_1611_, v_a_u2085_1612_);
return v___x_1613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2086___redArg___lam__0(lean_object* v_inst_1614_, lean_object* v_inst_1615_, lean_object* v_a_u2086_1616_, lean_object* v_____do__lift_1617_){
_start:
{
lean_object* v___x_1618_; 
v___x_1618_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1614_, v_inst_1615_, v_____do__lift_1617_, v_a_u2086_1616_);
return v___x_1618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2086___redArg(lean_object* v_inst_1619_, lean_object* v_inst_1620_, lean_object* v_f_1621_, lean_object* v_a_u2081_1622_, lean_object* v_a_u2082_1623_, lean_object* v_a_u2083_1624_, lean_object* v_a_u2084_1625_, lean_object* v_a_u2085_1626_, lean_object* v_a_u2086_1627_){
_start:
{
lean_object* v_toBind_1628_; lean_object* v___f_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; 
v_toBind_1628_ = lean_ctor_get(v_inst_1620_, 1);
lean_inc(v_toBind_1628_);
lean_inc_ref(v_inst_1620_);
lean_inc_ref(v_inst_1619_);
v___f_1629_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2086___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1629_, 0, v_inst_1619_);
lean_closure_set(v___f_1629_, 1, v_inst_1620_);
lean_closure_set(v___f_1629_, 2, v_a_u2086_1627_);
v___x_1630_ = l_Lean_Meta_Sym_Internal_mkAppS_u2085___redArg(v_inst_1619_, v_inst_1620_, v_f_1621_, v_a_u2081_1622_, v_a_u2082_1623_, v_a_u2083_1624_, v_a_u2084_1625_, v_a_u2085_1626_);
v___x_1631_ = lean_apply_4(v_toBind_1628_, lean_box(0), lean_box(0), v___x_1630_, v___f_1629_);
return v___x_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2086(lean_object* v_m_1632_, lean_object* v_inst_1633_, lean_object* v_inst_1634_, lean_object* v_f_1635_, lean_object* v_a_u2081_1636_, lean_object* v_a_u2082_1637_, lean_object* v_a_u2083_1638_, lean_object* v_a_u2084_1639_, lean_object* v_a_u2085_1640_, lean_object* v_a_u2086_1641_){
_start:
{
lean_object* v___x_1642_; 
v___x_1642_ = l_Lean_Meta_Sym_Internal_mkAppS_u2086___redArg(v_inst_1633_, v_inst_1634_, v_f_1635_, v_a_u2081_1636_, v_a_u2082_1637_, v_a_u2083_1638_, v_a_u2084_1639_, v_a_u2085_1640_, v_a_u2086_1641_);
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2087___redArg___lam__0(lean_object* v_inst_1643_, lean_object* v_inst_1644_, lean_object* v_a_u2087_1645_, lean_object* v_____do__lift_1646_){
_start:
{
lean_object* v___x_1647_; 
v___x_1647_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1643_, v_inst_1644_, v_____do__lift_1646_, v_a_u2087_1645_);
return v___x_1647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2087___redArg(lean_object* v_inst_1648_, lean_object* v_inst_1649_, lean_object* v_f_1650_, lean_object* v_a_u2081_1651_, lean_object* v_a_u2082_1652_, lean_object* v_a_u2083_1653_, lean_object* v_a_u2084_1654_, lean_object* v_a_u2085_1655_, lean_object* v_a_u2086_1656_, lean_object* v_a_u2087_1657_){
_start:
{
lean_object* v_toBind_1658_; lean_object* v___f_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; 
v_toBind_1658_ = lean_ctor_get(v_inst_1649_, 1);
lean_inc(v_toBind_1658_);
lean_inc_ref(v_inst_1649_);
lean_inc_ref(v_inst_1648_);
v___f_1659_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2087___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1659_, 0, v_inst_1648_);
lean_closure_set(v___f_1659_, 1, v_inst_1649_);
lean_closure_set(v___f_1659_, 2, v_a_u2087_1657_);
v___x_1660_ = l_Lean_Meta_Sym_Internal_mkAppS_u2086___redArg(v_inst_1648_, v_inst_1649_, v_f_1650_, v_a_u2081_1651_, v_a_u2082_1652_, v_a_u2083_1653_, v_a_u2084_1654_, v_a_u2085_1655_, v_a_u2086_1656_);
v___x_1661_ = lean_apply_4(v_toBind_1658_, lean_box(0), lean_box(0), v___x_1660_, v___f_1659_);
return v___x_1661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2087(lean_object* v_m_1662_, lean_object* v_inst_1663_, lean_object* v_inst_1664_, lean_object* v_f_1665_, lean_object* v_a_u2081_1666_, lean_object* v_a_u2082_1667_, lean_object* v_a_u2083_1668_, lean_object* v_a_u2084_1669_, lean_object* v_a_u2085_1670_, lean_object* v_a_u2086_1671_, lean_object* v_a_u2087_1672_){
_start:
{
lean_object* v___x_1673_; 
v___x_1673_ = l_Lean_Meta_Sym_Internal_mkAppS_u2087___redArg(v_inst_1663_, v_inst_1664_, v_f_1665_, v_a_u2081_1666_, v_a_u2082_1667_, v_a_u2083_1668_, v_a_u2084_1669_, v_a_u2085_1670_, v_a_u2086_1671_, v_a_u2087_1672_);
return v___x_1673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2088___redArg___lam__0(lean_object* v_inst_1674_, lean_object* v_inst_1675_, lean_object* v_a_u2088_1676_, lean_object* v_____do__lift_1677_){
_start:
{
lean_object* v___x_1678_; 
v___x_1678_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1674_, v_inst_1675_, v_____do__lift_1677_, v_a_u2088_1676_);
return v___x_1678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2088___redArg(lean_object* v_inst_1679_, lean_object* v_inst_1680_, lean_object* v_f_1681_, lean_object* v_a_u2081_1682_, lean_object* v_a_u2082_1683_, lean_object* v_a_u2083_1684_, lean_object* v_a_u2084_1685_, lean_object* v_a_u2085_1686_, lean_object* v_a_u2086_1687_, lean_object* v_a_u2087_1688_, lean_object* v_a_u2088_1689_){
_start:
{
lean_object* v_toBind_1690_; lean_object* v___f_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; 
v_toBind_1690_ = lean_ctor_get(v_inst_1680_, 1);
lean_inc(v_toBind_1690_);
lean_inc_ref(v_inst_1680_);
lean_inc_ref(v_inst_1679_);
v___f_1691_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2088___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1691_, 0, v_inst_1679_);
lean_closure_set(v___f_1691_, 1, v_inst_1680_);
lean_closure_set(v___f_1691_, 2, v_a_u2088_1689_);
v___x_1692_ = l_Lean_Meta_Sym_Internal_mkAppS_u2087___redArg(v_inst_1679_, v_inst_1680_, v_f_1681_, v_a_u2081_1682_, v_a_u2082_1683_, v_a_u2083_1684_, v_a_u2084_1685_, v_a_u2085_1686_, v_a_u2086_1687_, v_a_u2087_1688_);
v___x_1693_ = lean_apply_4(v_toBind_1690_, lean_box(0), lean_box(0), v___x_1692_, v___f_1691_);
return v___x_1693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2088(lean_object* v_m_1694_, lean_object* v_inst_1695_, lean_object* v_inst_1696_, lean_object* v_f_1697_, lean_object* v_a_u2081_1698_, lean_object* v_a_u2082_1699_, lean_object* v_a_u2083_1700_, lean_object* v_a_u2084_1701_, lean_object* v_a_u2085_1702_, lean_object* v_a_u2086_1703_, lean_object* v_a_u2087_1704_, lean_object* v_a_u2088_1705_){
_start:
{
lean_object* v___x_1706_; 
v___x_1706_ = l_Lean_Meta_Sym_Internal_mkAppS_u2088___redArg(v_inst_1695_, v_inst_1696_, v_f_1697_, v_a_u2081_1698_, v_a_u2082_1699_, v_a_u2083_1700_, v_a_u2084_1701_, v_a_u2085_1702_, v_a_u2086_1703_, v_a_u2087_1704_, v_a_u2088_1705_);
return v___x_1706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2089___redArg___lam__0(lean_object* v_inst_1707_, lean_object* v_inst_1708_, lean_object* v_a_u2089_1709_, lean_object* v_____do__lift_1710_){
_start:
{
lean_object* v___x_1711_; 
v___x_1711_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1707_, v_inst_1708_, v_____do__lift_1710_, v_a_u2089_1709_);
return v___x_1711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2089___redArg(lean_object* v_inst_1712_, lean_object* v_inst_1713_, lean_object* v_f_1714_, lean_object* v_a_u2081_1715_, lean_object* v_a_u2082_1716_, lean_object* v_a_u2083_1717_, lean_object* v_a_u2084_1718_, lean_object* v_a_u2085_1719_, lean_object* v_a_u2086_1720_, lean_object* v_a_u2087_1721_, lean_object* v_a_u2088_1722_, lean_object* v_a_u2089_1723_){
_start:
{
lean_object* v_toBind_1724_; lean_object* v___f_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; 
v_toBind_1724_ = lean_ctor_get(v_inst_1713_, 1);
lean_inc(v_toBind_1724_);
lean_inc_ref(v_inst_1713_);
lean_inc_ref(v_inst_1712_);
v___f_1725_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2089___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1725_, 0, v_inst_1712_);
lean_closure_set(v___f_1725_, 1, v_inst_1713_);
lean_closure_set(v___f_1725_, 2, v_a_u2089_1723_);
v___x_1726_ = l_Lean_Meta_Sym_Internal_mkAppS_u2088___redArg(v_inst_1712_, v_inst_1713_, v_f_1714_, v_a_u2081_1715_, v_a_u2082_1716_, v_a_u2083_1717_, v_a_u2084_1718_, v_a_u2085_1719_, v_a_u2086_1720_, v_a_u2087_1721_, v_a_u2088_1722_);
v___x_1727_ = lean_apply_4(v_toBind_1724_, lean_box(0), lean_box(0), v___x_1726_, v___f_1725_);
return v___x_1727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2089(lean_object* v_m_1728_, lean_object* v_inst_1729_, lean_object* v_inst_1730_, lean_object* v_f_1731_, lean_object* v_a_u2081_1732_, lean_object* v_a_u2082_1733_, lean_object* v_a_u2083_1734_, lean_object* v_a_u2084_1735_, lean_object* v_a_u2085_1736_, lean_object* v_a_u2086_1737_, lean_object* v_a_u2087_1738_, lean_object* v_a_u2088_1739_, lean_object* v_a_u2089_1740_){
_start:
{
lean_object* v___x_1741_; 
v___x_1741_ = l_Lean_Meta_Sym_Internal_mkAppS_u2089___redArg(v_inst_1729_, v_inst_1730_, v_f_1731_, v_a_u2081_1732_, v_a_u2082_1733_, v_a_u2083_1734_, v_a_u2084_1735_, v_a_u2085_1736_, v_a_u2086_1737_, v_a_u2087_1738_, v_a_u2088_1739_, v_a_u2089_1740_);
return v___x_1741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2080___redArg___lam__0(lean_object* v_inst_1742_, lean_object* v_inst_1743_, lean_object* v_a_u2081_u2080_1744_, lean_object* v_____do__lift_1745_){
_start:
{
lean_object* v___x_1746_; 
v___x_1746_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1742_, v_inst_1743_, v_____do__lift_1745_, v_a_u2081_u2080_1744_);
return v___x_1746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2080___redArg(lean_object* v_inst_1747_, lean_object* v_inst_1748_, lean_object* v_f_1749_, lean_object* v_a_u2081_1750_, lean_object* v_a_u2082_1751_, lean_object* v_a_u2083_1752_, lean_object* v_a_u2084_1753_, lean_object* v_a_u2085_1754_, lean_object* v_a_u2086_1755_, lean_object* v_a_u2087_1756_, lean_object* v_a_u2088_1757_, lean_object* v_a_u2089_1758_, lean_object* v_a_u2081_u2080_1759_){
_start:
{
lean_object* v_toBind_1760_; lean_object* v___f_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; 
v_toBind_1760_ = lean_ctor_get(v_inst_1748_, 1);
lean_inc(v_toBind_1760_);
lean_inc_ref(v_inst_1748_);
lean_inc_ref(v_inst_1747_);
v___f_1761_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2080___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1761_, 0, v_inst_1747_);
lean_closure_set(v___f_1761_, 1, v_inst_1748_);
lean_closure_set(v___f_1761_, 2, v_a_u2081_u2080_1759_);
v___x_1762_ = l_Lean_Meta_Sym_Internal_mkAppS_u2089___redArg(v_inst_1747_, v_inst_1748_, v_f_1749_, v_a_u2081_1750_, v_a_u2082_1751_, v_a_u2083_1752_, v_a_u2084_1753_, v_a_u2085_1754_, v_a_u2086_1755_, v_a_u2087_1756_, v_a_u2088_1757_, v_a_u2089_1758_);
v___x_1763_ = lean_apply_4(v_toBind_1760_, lean_box(0), lean_box(0), v___x_1762_, v___f_1761_);
return v___x_1763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2080(lean_object* v_m_1764_, lean_object* v_inst_1765_, lean_object* v_inst_1766_, lean_object* v_f_1767_, lean_object* v_a_u2081_1768_, lean_object* v_a_u2082_1769_, lean_object* v_a_u2083_1770_, lean_object* v_a_u2084_1771_, lean_object* v_a_u2085_1772_, lean_object* v_a_u2086_1773_, lean_object* v_a_u2087_1774_, lean_object* v_a_u2088_1775_, lean_object* v_a_u2089_1776_, lean_object* v_a_u2081_u2080_1777_){
_start:
{
lean_object* v___x_1778_; 
v___x_1778_ = l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2080___redArg(v_inst_1765_, v_inst_1766_, v_f_1767_, v_a_u2081_1768_, v_a_u2082_1769_, v_a_u2083_1770_, v_a_u2084_1771_, v_a_u2085_1772_, v_a_u2086_1773_, v_a_u2087_1774_, v_a_u2088_1775_, v_a_u2089_1776_, v_a_u2081_u2080_1777_);
return v___x_1778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2081___redArg___lam__0(lean_object* v_inst_1779_, lean_object* v_inst_1780_, lean_object* v_a_u2081_u2081_1781_, lean_object* v_____do__lift_1782_){
_start:
{
lean_object* v___x_1783_; 
v___x_1783_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1779_, v_inst_1780_, v_____do__lift_1782_, v_a_u2081_u2081_1781_);
return v___x_1783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2081___redArg(lean_object* v_inst_1784_, lean_object* v_inst_1785_, lean_object* v_f_1786_, lean_object* v_a_u2081_1787_, lean_object* v_a_u2082_1788_, lean_object* v_a_u2083_1789_, lean_object* v_a_u2084_1790_, lean_object* v_a_u2085_1791_, lean_object* v_a_u2086_1792_, lean_object* v_a_u2087_1793_, lean_object* v_a_u2088_1794_, lean_object* v_a_u2089_1795_, lean_object* v_a_u2081_u2080_1796_, lean_object* v_a_u2081_u2081_1797_){
_start:
{
lean_object* v_toBind_1798_; lean_object* v___f_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; 
v_toBind_1798_ = lean_ctor_get(v_inst_1785_, 1);
lean_inc(v_toBind_1798_);
lean_inc_ref(v_inst_1785_);
lean_inc_ref(v_inst_1784_);
v___f_1799_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2081___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1799_, 0, v_inst_1784_);
lean_closure_set(v___f_1799_, 1, v_inst_1785_);
lean_closure_set(v___f_1799_, 2, v_a_u2081_u2081_1797_);
v___x_1800_ = l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2080___redArg(v_inst_1784_, v_inst_1785_, v_f_1786_, v_a_u2081_1787_, v_a_u2082_1788_, v_a_u2083_1789_, v_a_u2084_1790_, v_a_u2085_1791_, v_a_u2086_1792_, v_a_u2087_1793_, v_a_u2088_1794_, v_a_u2089_1795_, v_a_u2081_u2080_1796_);
v___x_1801_ = lean_apply_4(v_toBind_1798_, lean_box(0), lean_box(0), v___x_1800_, v___f_1799_);
return v___x_1801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2081(lean_object* v_m_1802_, lean_object* v_inst_1803_, lean_object* v_inst_1804_, lean_object* v_f_1805_, lean_object* v_a_u2081_1806_, lean_object* v_a_u2082_1807_, lean_object* v_a_u2083_1808_, lean_object* v_a_u2084_1809_, lean_object* v_a_u2085_1810_, lean_object* v_a_u2086_1811_, lean_object* v_a_u2087_1812_, lean_object* v_a_u2088_1813_, lean_object* v_a_u2089_1814_, lean_object* v_a_u2081_u2080_1815_, lean_object* v_a_u2081_u2081_1816_){
_start:
{
lean_object* v___x_1817_; 
v___x_1817_ = l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2081___redArg(v_inst_1803_, v_inst_1804_, v_f_1805_, v_a_u2081_1806_, v_a_u2082_1807_, v_a_u2083_1808_, v_a_u2084_1809_, v_a_u2085_1810_, v_a_u2086_1811_, v_a_u2087_1812_, v_a_u2088_1813_, v_a_u2089_1814_, v_a_u2081_u2080_1815_, v_a_u2081_u2081_1816_);
return v___x_1817_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg___lam__0___boxed(lean_object* v_i_1818_, lean_object* v_inst_1819_, lean_object* v_inst_1820_, lean_object* v_args_1821_, lean_object* v_endIdx_1822_, lean_object* v_____do__lift_1823_){
_start:
{
lean_object* v_res_1824_; 
v_res_1824_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg___lam__0(v_i_1818_, v_inst_1819_, v_inst_1820_, v_args_1821_, v_endIdx_1822_, v_____do__lift_1823_);
lean_dec(v_i_1818_);
return v_res_1824_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg(lean_object* v_inst_1825_, lean_object* v_inst_1826_, lean_object* v_args_1827_, lean_object* v_endIdx_1828_, lean_object* v_b_1829_, lean_object* v_i_1830_){
_start:
{
uint8_t v___x_1831_; 
v___x_1831_ = lean_nat_dec_le(v_endIdx_1828_, v_i_1830_);
if (v___x_1831_ == 0)
{
lean_object* v_toBind_1832_; lean_object* v___f_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; 
v_toBind_1832_ = lean_ctor_get(v_inst_1826_, 1);
lean_inc(v_toBind_1832_);
lean_inc_ref(v_args_1827_);
lean_inc_ref(v_inst_1826_);
lean_inc_ref(v_inst_1825_);
lean_inc(v_i_1830_);
v___f_1833_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1833_, 0, v_i_1830_);
lean_closure_set(v___f_1833_, 1, v_inst_1825_);
lean_closure_set(v___f_1833_, 2, v_inst_1826_);
lean_closure_set(v___f_1833_, 3, v_args_1827_);
lean_closure_set(v___f_1833_, 4, v_endIdx_1828_);
v___x_1834_ = l_Lean_instInhabitedExpr;
v___x_1835_ = lean_array_get(v___x_1834_, v_args_1827_, v_i_1830_);
lean_dec(v_i_1830_);
lean_dec_ref(v_args_1827_);
v___x_1836_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1825_, v_inst_1826_, v_b_1829_, v___x_1835_);
v___x_1837_ = lean_apply_4(v_toBind_1832_, lean_box(0), lean_box(0), v___x_1836_, v___f_1833_);
return v___x_1837_;
}
else
{
lean_object* v_toApplicative_1838_; lean_object* v_toPure_1839_; lean_object* v___x_1840_; 
lean_dec(v_i_1830_);
lean_dec(v_endIdx_1828_);
lean_dec_ref(v_args_1827_);
lean_dec_ref(v_inst_1825_);
v_toApplicative_1838_ = lean_ctor_get(v_inst_1826_, 0);
lean_inc_ref(v_toApplicative_1838_);
lean_dec_ref(v_inst_1826_);
v_toPure_1839_ = lean_ctor_get(v_toApplicative_1838_, 1);
lean_inc(v_toPure_1839_);
lean_dec_ref(v_toApplicative_1838_);
v___x_1840_ = lean_apply_2(v_toPure_1839_, lean_box(0), v_b_1829_);
return v___x_1840_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg___lam__0(lean_object* v_i_1841_, lean_object* v_inst_1842_, lean_object* v_inst_1843_, lean_object* v_args_1844_, lean_object* v_endIdx_1845_, lean_object* v_____do__lift_1846_){
_start:
{
lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; 
v___x_1847_ = lean_unsigned_to_nat(1u);
v___x_1848_ = lean_nat_add(v_i_1841_, v___x_1847_);
v___x_1849_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg(v_inst_1842_, v_inst_1843_, v_args_1844_, v_endIdx_1845_, v_____do__lift_1846_, v___x_1848_);
return v___x_1849_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go(lean_object* v_m_1850_, lean_object* v_inst_1851_, lean_object* v_inst_1852_, lean_object* v_args_1853_, lean_object* v_endIdx_1854_, lean_object* v_b_1855_, lean_object* v_i_1856_){
_start:
{
lean_object* v___x_1857_; 
v___x_1857_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg(v_inst_1851_, v_inst_1852_, v_args_1853_, v_endIdx_1854_, v_b_1855_, v_i_1856_);
return v___x_1857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRangeS___redArg(lean_object* v_inst_1858_, lean_object* v_inst_1859_, lean_object* v_f_1860_, lean_object* v_beginIdx_1861_, lean_object* v_endIdx_1862_, lean_object* v_args_1863_){
_start:
{
lean_object* v___x_1864_; 
v___x_1864_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg(v_inst_1858_, v_inst_1859_, v_args_1863_, v_endIdx_1862_, v_f_1860_, v_beginIdx_1861_);
return v___x_1864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRangeS(lean_object* v_m_1865_, lean_object* v_inst_1866_, lean_object* v_inst_1867_, lean_object* v_f_1868_, lean_object* v_beginIdx_1869_, lean_object* v_endIdx_1870_, lean_object* v_args_1871_){
_start:
{
lean_object* v___x_1872_; 
v___x_1872_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg(v_inst_1866_, v_inst_1867_, v_args_1871_, v_endIdx_1870_, v_f_1868_, v_beginIdx_1869_);
return v___x_1872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___redArg(lean_object* v_inst_1873_, lean_object* v_inst_1874_, lean_object* v_f_1875_, lean_object* v_args_1876_){
_start:
{
lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; 
v___x_1877_ = lean_unsigned_to_nat(0u);
v___x_1878_ = lean_array_get_size(v_args_1876_);
v___x_1879_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg(v_inst_1873_, v_inst_1874_, v_args_1876_, v___x_1878_, v_f_1875_, v___x_1877_);
return v___x_1879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS(lean_object* v_m_1880_, lean_object* v_inst_1881_, lean_object* v_inst_1882_, lean_object* v_f_1883_, lean_object* v_args_1884_){
_start:
{
lean_object* v___x_1885_; 
v___x_1885_ = l_Lean_Meta_Sym_Internal_mkAppNS___redArg(v_inst_1881_, v_inst_1882_, v_f_1883_, v_args_1884_);
return v___x_1885_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg___lam__0___boxed(lean_object* v_inst_1886_, lean_object* v_inst_1887_, lean_object* v_revArgs_1888_, lean_object* v_start_1889_, lean_object* v_i_1890_, lean_object* v_____do__lift_1891_){
_start:
{
lean_object* v_res_1892_; 
v_res_1892_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg___lam__0(v_inst_1886_, v_inst_1887_, v_revArgs_1888_, v_start_1889_, v_i_1890_, v_____do__lift_1891_);
lean_dec(v_i_1890_);
return v_res_1892_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg(lean_object* v_inst_1893_, lean_object* v_inst_1894_, lean_object* v_revArgs_1895_, lean_object* v_start_1896_, lean_object* v_b_1897_, lean_object* v_i_1898_){
_start:
{
uint8_t v___x_1899_; 
v___x_1899_ = lean_nat_dec_le(v_i_1898_, v_start_1896_);
if (v___x_1899_ == 0)
{
lean_object* v_toBind_1900_; lean_object* v___x_1901_; lean_object* v_i_1902_; lean_object* v___f_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; 
v_toBind_1900_ = lean_ctor_get(v_inst_1894_, 1);
lean_inc(v_toBind_1900_);
v___x_1901_ = lean_unsigned_to_nat(1u);
v_i_1902_ = lean_nat_sub(v_i_1898_, v___x_1901_);
lean_inc(v_i_1902_);
lean_inc_ref(v_revArgs_1895_);
lean_inc_ref(v_inst_1894_);
lean_inc_ref(v_inst_1893_);
v___f_1903_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1903_, 0, v_inst_1893_);
lean_closure_set(v___f_1903_, 1, v_inst_1894_);
lean_closure_set(v___f_1903_, 2, v_revArgs_1895_);
lean_closure_set(v___f_1903_, 3, v_start_1896_);
lean_closure_set(v___f_1903_, 4, v_i_1902_);
v___x_1904_ = l_Lean_instInhabitedExpr;
v___x_1905_ = lean_array_get(v___x_1904_, v_revArgs_1895_, v_i_1902_);
lean_dec(v_i_1902_);
lean_dec_ref(v_revArgs_1895_);
v___x_1906_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1893_, v_inst_1894_, v_b_1897_, v___x_1905_);
v___x_1907_ = lean_apply_4(v_toBind_1900_, lean_box(0), lean_box(0), v___x_1906_, v___f_1903_);
return v___x_1907_;
}
else
{
lean_object* v_toApplicative_1908_; lean_object* v_toPure_1909_; lean_object* v___x_1910_; 
lean_dec(v_start_1896_);
lean_dec_ref(v_revArgs_1895_);
lean_dec_ref(v_inst_1893_);
v_toApplicative_1908_ = lean_ctor_get(v_inst_1894_, 0);
lean_inc_ref(v_toApplicative_1908_);
lean_dec_ref(v_inst_1894_);
v_toPure_1909_ = lean_ctor_get(v_toApplicative_1908_, 1);
lean_inc(v_toPure_1909_);
lean_dec_ref(v_toApplicative_1908_);
v___x_1910_ = lean_apply_2(v_toPure_1909_, lean_box(0), v_b_1897_);
return v___x_1910_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg___lam__0(lean_object* v_inst_1911_, lean_object* v_inst_1912_, lean_object* v_revArgs_1913_, lean_object* v_start_1914_, lean_object* v_i_1915_, lean_object* v_____do__lift_1916_){
_start:
{
lean_object* v___x_1917_; 
v___x_1917_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg(v_inst_1911_, v_inst_1912_, v_revArgs_1913_, v_start_1914_, v_____do__lift_1916_, v_i_1915_);
return v___x_1917_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg___boxed(lean_object* v_inst_1918_, lean_object* v_inst_1919_, lean_object* v_revArgs_1920_, lean_object* v_start_1921_, lean_object* v_b_1922_, lean_object* v_i_1923_){
_start:
{
lean_object* v_res_1924_; 
v_res_1924_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg(v_inst_1918_, v_inst_1919_, v_revArgs_1920_, v_start_1921_, v_b_1922_, v_i_1923_);
lean_dec(v_i_1923_);
return v_res_1924_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go(lean_object* v_m_1925_, lean_object* v_inst_1926_, lean_object* v_inst_1927_, lean_object* v_revArgs_1928_, lean_object* v_start_1929_, lean_object* v_b_1930_, lean_object* v_i_1931_){
_start:
{
lean_object* v___x_1932_; 
v___x_1932_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg(v_inst_1926_, v_inst_1927_, v_revArgs_1928_, v_start_1929_, v_b_1930_, v_i_1931_);
return v___x_1932_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___boxed(lean_object* v_m_1933_, lean_object* v_inst_1934_, lean_object* v_inst_1935_, lean_object* v_revArgs_1936_, lean_object* v_start_1937_, lean_object* v_b_1938_, lean_object* v_i_1939_){
_start:
{
lean_object* v_res_1940_; 
v_res_1940_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go(v_m_1933_, v_inst_1934_, v_inst_1935_, v_revArgs_1936_, v_start_1937_, v_b_1938_, v_i_1939_);
lean_dec(v_i_1939_);
return v_res_1940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevRangeS___redArg(lean_object* v_inst_1941_, lean_object* v_inst_1942_, lean_object* v_f_1943_, lean_object* v_beginIdx_1944_, lean_object* v_endIdx_1945_, lean_object* v_revArgs_1946_){
_start:
{
lean_object* v___x_1947_; 
v___x_1947_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg(v_inst_1941_, v_inst_1942_, v_revArgs_1946_, v_beginIdx_1944_, v_f_1943_, v_endIdx_1945_);
return v___x_1947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevRangeS___redArg___boxed(lean_object* v_inst_1948_, lean_object* v_inst_1949_, lean_object* v_f_1950_, lean_object* v_beginIdx_1951_, lean_object* v_endIdx_1952_, lean_object* v_revArgs_1953_){
_start:
{
lean_object* v_res_1954_; 
v_res_1954_ = l_Lean_Meta_Sym_Internal_mkAppRevRangeS___redArg(v_inst_1948_, v_inst_1949_, v_f_1950_, v_beginIdx_1951_, v_endIdx_1952_, v_revArgs_1953_);
lean_dec(v_endIdx_1952_);
return v_res_1954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevRangeS(lean_object* v_m_1955_, lean_object* v_inst_1956_, lean_object* v_inst_1957_, lean_object* v_f_1958_, lean_object* v_beginIdx_1959_, lean_object* v_endIdx_1960_, lean_object* v_revArgs_1961_){
_start:
{
lean_object* v___x_1962_; 
v___x_1962_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg(v_inst_1956_, v_inst_1957_, v_revArgs_1961_, v_beginIdx_1959_, v_f_1958_, v_endIdx_1960_);
return v___x_1962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevRangeS___boxed(lean_object* v_m_1963_, lean_object* v_inst_1964_, lean_object* v_inst_1965_, lean_object* v_f_1966_, lean_object* v_beginIdx_1967_, lean_object* v_endIdx_1968_, lean_object* v_revArgs_1969_){
_start:
{
lean_object* v_res_1970_; 
v_res_1970_ = l_Lean_Meta_Sym_Internal_mkAppRevRangeS(v_m_1963_, v_inst_1964_, v_inst_1965_, v_f_1966_, v_beginIdx_1967_, v_endIdx_1968_, v_revArgs_1969_);
lean_dec(v_endIdx_1968_);
return v_res_1970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevS___redArg(lean_object* v_inst_1971_, lean_object* v_inst_1972_, lean_object* v_f_1973_, lean_object* v_revArgs_1974_){
_start:
{
lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; 
v___x_1975_ = lean_unsigned_to_nat(0u);
v___x_1976_ = lean_array_get_size(v_revArgs_1974_);
v___x_1977_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg(v_inst_1971_, v_inst_1972_, v_revArgs_1974_, v___x_1975_, v_f_1973_, v___x_1976_);
return v___x_1977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevS(lean_object* v_m_1978_, lean_object* v_inst_1979_, lean_object* v_inst_1980_, lean_object* v_f_1981_, lean_object* v_revArgs_1982_){
_start:
{
lean_object* v___x_1983_; 
v___x_1983_ = l_Lean_Meta_Sym_Internal_mkAppRevS___redArg(v_inst_1979_, v_inst_1980_, v_f_1981_, v_revArgs_1982_);
return v___x_1983_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy = _init_l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy();
lean_mark_persistent(l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy);
l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM = _init_l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM();
lean_mark_persistent(l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
}
#ifdef __cplusplus
}
#endif
