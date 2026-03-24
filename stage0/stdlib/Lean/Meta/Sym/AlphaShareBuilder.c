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
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash___boxed(lean_object*);
lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
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
lean_inc(v_inst_11_);
v___f_19_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_instMonadShareCommonOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_19_, 0, v_share1_13_);
lean_closure_set(v___f_19_, 1, v_inst_11_);
lean_inc(v_inst_11_);
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
lean_inc(v_inst_28_);
v___f_36_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_instMonadShareCommonOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_36_, 0, v_share1_30_);
lean_closure_set(v___f_36_, 1, v_inst_28_);
lean_inc(v_inst_28_);
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
size_t v_x_2143__boxed_197_; size_t v_x_2144__boxed_198_; lean_object* v_res_199_; 
v_x_2143__boxed_197_ = lean_unbox_usize(v_x_193_);
lean_dec(v_x_193_);
v_x_2144__boxed_198_ = lean_unbox_usize(v_x_194_);
lean_dec(v_x_194_);
v_res_199_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg(v_x_192_, v_x_2143__boxed_197_, v_x_2144__boxed_198_, v_x_195_, v_x_196_);
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
lean_inc(v_key_234_);
lean_dec_ref(v___x_233_);
lean_inc(v_key_234_);
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
size_t v_x_2337__boxed_246_; lean_object* v_res_247_; 
v_x_2337__boxed_246_ = lean_unbox_usize(v_x_243_);
lean_dec(v_x_243_);
v_res_247_ = l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg(v_x_242_, v_x_2337__boxed_246_, v_x_244_, v_x_245_);
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
lean_object* v___x_259_; lean_object* v_share_260_; lean_object* v_maxFVar_261_; lean_object* v_proofInstInfo_262_; lean_object* v_inferType_263_; lean_object* v_getLevel_264_; lean_object* v_congrInfo_265_; lean_object* v_defEqI_266_; lean_object* v_extensions_267_; uint8_t v_debug_268_; lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_279_; 
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
v_debug_268_ = lean_ctor_get_uint8(v___x_259_, sizeof(void*)*8);
v_isSharedCheck_279_ = !lean_is_exclusive(v___x_259_);
if (v_isSharedCheck_279_ == 0)
{
v___x_270_ = v___x_259_;
v_isShared_271_ = v_isSharedCheck_279_;
goto v_resetjp_269_;
}
else
{
lean_inc(v_extensions_267_);
lean_inc(v_defEqI_266_);
lean_inc(v_congrInfo_265_);
lean_inc(v_getLevel_264_);
lean_inc(v_inferType_263_);
lean_inc(v_proofInstInfo_262_);
lean_inc(v_maxFVar_261_);
lean_inc(v_share_260_);
lean_dec(v___x_259_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_279_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_275_; 
v___x_272_ = lean_box(0);
lean_inc_ref(v_e_248_);
v___x_273_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1___redArg(v_share_260_, v_e_248_, v___x_272_);
if (v_isShared_271_ == 0)
{
lean_ctor_set(v___x_270_, 0, v___x_273_);
v___x_275_ = v___x_270_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v___x_273_);
lean_ctor_set(v_reuseFailAlloc_278_, 1, v_maxFVar_261_);
lean_ctor_set(v_reuseFailAlloc_278_, 2, v_proofInstInfo_262_);
lean_ctor_set(v_reuseFailAlloc_278_, 3, v_inferType_263_);
lean_ctor_set(v_reuseFailAlloc_278_, 4, v_getLevel_264_);
lean_ctor_set(v_reuseFailAlloc_278_, 5, v_congrInfo_265_);
lean_ctor_set(v_reuseFailAlloc_278_, 6, v_defEqI_266_);
lean_ctor_set(v_reuseFailAlloc_278_, 7, v_extensions_267_);
lean_ctor_set_uint8(v_reuseFailAlloc_278_, sizeof(void*)*8, v_debug_268_);
v___x_275_ = v_reuseFailAlloc_278_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_276_ = lean_st_ref_set(v_a_249_, v___x_275_);
v___x_277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_277_, 0, v_e_248_);
return v___x_277_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg___boxed(lean_object* v_e_280_, lean_object* v_a_281_, lean_object* v_a_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v_e_280_, v_a_281_);
lean_dec(v_a_281_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Sym_share1(lean_object* v_e_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_){
_start:
{
lean_object* v___x_292_; 
v___x_292_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v_e_284_, v_a_286_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___boxed(lean_object* v_e_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l_Lean_Meta_Sym_Internal_Sym_share1(v_e_293_, v_a_294_, v_a_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_);
lean_dec(v_a_299_);
lean_dec_ref(v_a_298_);
lean_dec(v_a_297_);
lean_dec_ref(v_a_296_);
lean_dec(v_a_295_);
lean_dec_ref(v_a_294_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0(lean_object* v_00_u03b2_302_, lean_object* v_x_303_, size_t v_x_304_, lean_object* v_x_305_, lean_object* v_x_306_){
_start:
{
lean_object* v___x_307_; 
v___x_307_ = l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg(v_x_303_, v_x_304_, v_x_305_, v_x_306_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___boxed(lean_object* v_00_u03b2_308_, lean_object* v_x_309_, lean_object* v_x_310_, lean_object* v_x_311_, lean_object* v_x_312_){
_start:
{
size_t v_x_2427__boxed_313_; lean_object* v_res_314_; 
v_x_2427__boxed_313_ = lean_unbox_usize(v_x_310_);
lean_dec(v_x_310_);
v_res_314_ = l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0(v_00_u03b2_308_, v_x_309_, v_x_2427__boxed_313_, v_x_311_, v_x_312_);
lean_dec_ref(v_x_312_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1(lean_object* v_00_u03b2_315_, lean_object* v_x_316_, lean_object* v_x_317_, lean_object* v_x_318_){
_start:
{
lean_object* v___x_319_; 
v___x_319_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1___redArg(v_x_316_, v_x_317_, v_x_318_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0(lean_object* v_00_u03b2_320_, lean_object* v_keys_321_, lean_object* v_vals_322_, lean_object* v_heq_323_, lean_object* v_i_324_, lean_object* v_k_325_, lean_object* v_k_u2080_326_){
_start:
{
lean_object* v___x_327_; 
v___x_327_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0___redArg(v_keys_321_, v_i_324_, v_k_325_, v_k_u2080_326_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0___boxed(lean_object* v_00_u03b2_328_, lean_object* v_keys_329_, lean_object* v_vals_330_, lean_object* v_heq_331_, lean_object* v_i_332_, lean_object* v_k_333_, lean_object* v_k_u2080_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0(v_00_u03b2_328_, v_keys_329_, v_vals_330_, v_heq_331_, v_i_332_, v_k_333_, v_k_u2080_334_);
lean_dec_ref(v_k_u2080_334_);
lean_dec_ref(v_vals_330_);
lean_dec_ref(v_keys_329_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2(lean_object* v_00_u03b2_336_, lean_object* v_x_337_, size_t v_x_338_, size_t v_x_339_, lean_object* v_x_340_, lean_object* v_x_341_){
_start:
{
lean_object* v___x_342_; 
v___x_342_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg(v_x_337_, v_x_338_, v_x_339_, v_x_340_, v_x_341_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_343_, lean_object* v_x_344_, lean_object* v_x_345_, lean_object* v_x_346_, lean_object* v_x_347_, lean_object* v_x_348_){
_start:
{
size_t v_x_2451__boxed_349_; size_t v_x_2452__boxed_350_; lean_object* v_res_351_; 
v_x_2451__boxed_349_ = lean_unbox_usize(v_x_345_);
lean_dec(v_x_345_);
v_x_2452__boxed_350_ = lean_unbox_usize(v_x_346_);
lean_dec(v_x_346_);
v_res_351_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2(v_00_u03b2_343_, v_x_344_, v_x_2451__boxed_349_, v_x_2452__boxed_350_, v_x_347_, v_x_348_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_352_, lean_object* v_n_353_, lean_object* v_k_354_, lean_object* v_v_355_){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__3___redArg(v_n_353_, v_k_354_, v_v_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_357_, size_t v_depth_358_, lean_object* v_keys_359_, lean_object* v_vals_360_, lean_object* v_heq_361_, lean_object* v_i_362_, lean_object* v_entries_363_){
_start:
{
lean_object* v___x_364_; 
v___x_364_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4___redArg(v_depth_358_, v_keys_359_, v_vals_360_, v_i_362_, v_entries_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_365_, lean_object* v_depth_366_, lean_object* v_keys_367_, lean_object* v_vals_368_, lean_object* v_heq_369_, lean_object* v_i_370_, lean_object* v_entries_371_){
_start:
{
size_t v_depth_boxed_372_; lean_object* v_res_373_; 
v_depth_boxed_372_ = lean_unbox_usize(v_depth_366_);
lean_dec(v_depth_366_);
v_res_373_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4(v_00_u03b2_365_, v_depth_boxed_372_, v_keys_367_, v_vals_368_, v_heq_369_, v_i_370_, v_entries_371_);
lean_dec_ref(v_vals_368_);
lean_dec_ref(v_keys_367_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_374_, lean_object* v_x_375_, lean_object* v_x_376_, lean_object* v_x_377_, lean_object* v_x_378_){
_start:
{
lean_object* v___x_379_; 
v___x_379_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__3_spec__4___redArg(v_x_375_, v_x_376_, v_x_377_, v_x_378_);
return v___x_379_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0(void){
_start:
{
lean_object* v___x_380_; 
v___x_380_ = l_Lean_Meta_Sym_instInhabitedSymM(lean_box(0));
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0(lean_object* v_msg_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_){
_start:
{
lean_object* v___x_389_; lean_object* v___x_756__overap_390_; lean_object* v___x_391_; 
v___x_389_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0, &l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0);
v___x_756__overap_390_ = lean_panic_fn(v___x_389_, v_msg_381_);
lean_inc(v___y_387_);
lean_inc_ref(v___y_386_);
lean_inc(v___y_385_);
lean_inc_ref(v___y_384_);
lean_inc(v___y_383_);
lean_inc_ref(v___y_382_);
v___x_391_ = lean_apply_7(v___x_756__overap_390_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, lean_box(0));
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___boxed(lean_object* v_msg_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0(v_msg_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_);
lean_dec(v___y_398_);
lean_dec_ref(v___y_397_);
lean_dec(v___y_396_);
lean_dec_ref(v___y_395_);
lean_dec(v___y_394_);
lean_dec_ref(v___y_393_);
return v_res_400_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__3(void){
_start:
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_404_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__2));
v___x_405_ = lean_unsigned_to_nat(2u);
v___x_406_ = lean_unsigned_to_nat(42u);
v___x_407_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__1));
v___x_408_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_409_ = l_mkPanicMessageWithDecl(v___x_408_, v___x_407_, v___x_406_, v___x_405_, v___x_404_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object* v_e_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_){
_start:
{
lean_object* v___x_418_; lean_object* v_share_419_; lean_object* v___x_420_; uint64_t v___x_421_; size_t v___x_422_; lean_object* v___x_423_; uint8_t v___x_424_; 
v___x_418_ = lean_st_ref_get(v_a_412_);
v_share_419_ = lean_ctor_get(v___x_418_, 0);
lean_inc_ref(v_share_419_);
lean_dec(v___x_418_);
v___x_420_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy;
v___x_421_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_410_);
v___x_422_ = lean_uint64_to_usize(v___x_421_);
lean_inc_ref(v_e_410_);
v___x_423_ = l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg(v_share_419_, v___x_422_, v_e_410_, v___x_420_);
v___x_424_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_423_, v_e_410_);
lean_dec_ref(v_e_410_);
lean_dec_ref(v___x_423_);
if (v___x_424_ == 0)
{
lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_425_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__3, &l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__3_once, _init_l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__3);
v___x_426_ = l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0(v___x_425_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_);
return v___x_426_;
}
else
{
lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_427_ = lean_box(0);
v___x_428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_428_, 0, v___x_427_);
return v___x_428_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared___boxed(lean_object* v_e_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_e_429_, v_a_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_);
lean_dec(v_a_435_);
lean_dec_ref(v_a_434_);
lean_dec(v_a_433_);
lean_dec_ref(v_a_432_);
lean_dec(v_a_431_);
lean_dec_ref(v_a_430_);
return v_res_437_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2(void){
_start:
{
lean_object* v___f_448_; lean_object* v___f_449_; lean_object* v___x_450_; 
v___f_448_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__1));
v___f_449_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__0));
v___x_450_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___f_449_, v___f_448_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM___redArg(lean_object* v_k_451_, lean_object* v_a_452_){
_start:
{
lean_object* v___x_454_; lean_object* v_share_455_; lean_object* v_maxFVar_456_; lean_object* v_proofInstInfo_457_; lean_object* v_inferType_458_; lean_object* v_getLevel_459_; lean_object* v_congrInfo_460_; lean_object* v_defEqI_461_; lean_object* v_extensions_462_; uint8_t v_debug_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_497_; 
v___x_454_ = lean_st_ref_take(v_a_452_);
v_share_455_ = lean_ctor_get(v___x_454_, 0);
v_maxFVar_456_ = lean_ctor_get(v___x_454_, 1);
v_proofInstInfo_457_ = lean_ctor_get(v___x_454_, 2);
v_inferType_458_ = lean_ctor_get(v___x_454_, 3);
v_getLevel_459_ = lean_ctor_get(v___x_454_, 4);
v_congrInfo_460_ = lean_ctor_get(v___x_454_, 5);
v_defEqI_461_ = lean_ctor_get(v___x_454_, 6);
v_extensions_462_ = lean_ctor_get(v___x_454_, 7);
v_debug_463_ = lean_ctor_get_uint8(v___x_454_, sizeof(void*)*8);
v_isSharedCheck_497_ = !lean_is_exclusive(v___x_454_);
if (v_isSharedCheck_497_ == 0)
{
v___x_465_ = v___x_454_;
v_isShared_466_ = v_isSharedCheck_497_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_extensions_462_);
lean_inc(v_defEqI_461_);
lean_inc(v_congrInfo_460_);
lean_inc(v_getLevel_459_);
lean_inc(v_inferType_458_);
lean_inc(v_proofInstInfo_457_);
lean_inc(v_maxFVar_456_);
lean_inc(v_share_455_);
lean_dec(v___x_454_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_497_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v___x_467_; lean_object* v___x_469_; 
v___x_467_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2, &l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2_once, _init_l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2);
if (v_isShared_466_ == 0)
{
lean_ctor_set(v___x_465_, 0, v___x_467_);
v___x_469_ = v___x_465_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v___x_467_);
lean_ctor_set(v_reuseFailAlloc_496_, 1, v_maxFVar_456_);
lean_ctor_set(v_reuseFailAlloc_496_, 2, v_proofInstInfo_457_);
lean_ctor_set(v_reuseFailAlloc_496_, 3, v_inferType_458_);
lean_ctor_set(v_reuseFailAlloc_496_, 4, v_getLevel_459_);
lean_ctor_set(v_reuseFailAlloc_496_, 5, v_congrInfo_460_);
lean_ctor_set(v_reuseFailAlloc_496_, 6, v_defEqI_461_);
lean_ctor_set(v_reuseFailAlloc_496_, 7, v_extensions_462_);
lean_ctor_set_uint8(v_reuseFailAlloc_496_, sizeof(void*)*8, v_debug_463_);
v___x_469_ = v_reuseFailAlloc_496_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
lean_object* v___x_470_; lean_object* v___x_471_; uint8_t v_debug_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v_fst_475_; lean_object* v_snd_476_; lean_object* v___x_477_; lean_object* v_maxFVar_478_; lean_object* v_proofInstInfo_479_; lean_object* v_inferType_480_; lean_object* v_getLevel_481_; lean_object* v_congrInfo_482_; lean_object* v_defEqI_483_; lean_object* v_extensions_484_; uint8_t v_debug_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_494_; 
v___x_470_ = lean_st_ref_set(v_a_452_, v___x_469_);
v___x_471_ = lean_st_ref_get(v_a_452_);
v_debug_472_ = lean_ctor_get_uint8(v___x_471_, sizeof(void*)*8);
lean_dec(v___x_471_);
v___x_473_ = lean_box(v_debug_472_);
v___x_474_ = lean_apply_2(v_k_451_, v___x_473_, v_share_455_);
v_fst_475_ = lean_ctor_get(v___x_474_, 0);
lean_inc(v_fst_475_);
v_snd_476_ = lean_ctor_get(v___x_474_, 1);
lean_inc(v_snd_476_);
lean_dec_ref(v___x_474_);
v___x_477_ = lean_st_ref_take(v_a_452_);
v_maxFVar_478_ = lean_ctor_get(v___x_477_, 1);
v_proofInstInfo_479_ = lean_ctor_get(v___x_477_, 2);
v_inferType_480_ = lean_ctor_get(v___x_477_, 3);
v_getLevel_481_ = lean_ctor_get(v___x_477_, 4);
v_congrInfo_482_ = lean_ctor_get(v___x_477_, 5);
v_defEqI_483_ = lean_ctor_get(v___x_477_, 6);
v_extensions_484_ = lean_ctor_get(v___x_477_, 7);
v_debug_485_ = lean_ctor_get_uint8(v___x_477_, sizeof(void*)*8);
v_isSharedCheck_494_ = !lean_is_exclusive(v___x_477_);
if (v_isSharedCheck_494_ == 0)
{
lean_object* v_unused_495_; 
v_unused_495_ = lean_ctor_get(v___x_477_, 0);
lean_dec(v_unused_495_);
v___x_487_ = v___x_477_;
v_isShared_488_ = v_isSharedCheck_494_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_extensions_484_);
lean_inc(v_defEqI_483_);
lean_inc(v_congrInfo_482_);
lean_inc(v_getLevel_481_);
lean_inc(v_inferType_480_);
lean_inc(v_proofInstInfo_479_);
lean_inc(v_maxFVar_478_);
lean_dec(v___x_477_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_494_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v___x_490_; 
if (v_isShared_488_ == 0)
{
lean_ctor_set(v___x_487_, 0, v_snd_476_);
v___x_490_ = v___x_487_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v_snd_476_);
lean_ctor_set(v_reuseFailAlloc_493_, 1, v_maxFVar_478_);
lean_ctor_set(v_reuseFailAlloc_493_, 2, v_proofInstInfo_479_);
lean_ctor_set(v_reuseFailAlloc_493_, 3, v_inferType_480_);
lean_ctor_set(v_reuseFailAlloc_493_, 4, v_getLevel_481_);
lean_ctor_set(v_reuseFailAlloc_493_, 5, v_congrInfo_482_);
lean_ctor_set(v_reuseFailAlloc_493_, 6, v_defEqI_483_);
lean_ctor_set(v_reuseFailAlloc_493_, 7, v_extensions_484_);
lean_ctor_set_uint8(v_reuseFailAlloc_493_, sizeof(void*)*8, v_debug_485_);
v___x_490_ = v_reuseFailAlloc_493_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_491_ = lean_st_ref_set(v_a_452_, v___x_490_);
v___x_492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_492_, 0, v_fst_475_);
return v___x_492_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___boxed(lean_object* v_k_498_, lean_object* v_a_499_, lean_object* v_a_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_Lean_Meta_Sym_Internal_liftBuilderM___redArg(v_k_498_, v_a_499_);
lean_dec(v_a_499_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM(lean_object* v_00_u03b1_502_, lean_object* v_k_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_){
_start:
{
lean_object* v___x_511_; lean_object* v_share_512_; lean_object* v_maxFVar_513_; lean_object* v_proofInstInfo_514_; lean_object* v_inferType_515_; lean_object* v_getLevel_516_; lean_object* v_congrInfo_517_; lean_object* v_defEqI_518_; lean_object* v_extensions_519_; uint8_t v_debug_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_554_; 
v___x_511_ = lean_st_ref_take(v_a_505_);
v_share_512_ = lean_ctor_get(v___x_511_, 0);
v_maxFVar_513_ = lean_ctor_get(v___x_511_, 1);
v_proofInstInfo_514_ = lean_ctor_get(v___x_511_, 2);
v_inferType_515_ = lean_ctor_get(v___x_511_, 3);
v_getLevel_516_ = lean_ctor_get(v___x_511_, 4);
v_congrInfo_517_ = lean_ctor_get(v___x_511_, 5);
v_defEqI_518_ = lean_ctor_get(v___x_511_, 6);
v_extensions_519_ = lean_ctor_get(v___x_511_, 7);
v_debug_520_ = lean_ctor_get_uint8(v___x_511_, sizeof(void*)*8);
v_isSharedCheck_554_ = !lean_is_exclusive(v___x_511_);
if (v_isSharedCheck_554_ == 0)
{
v___x_522_ = v___x_511_;
v_isShared_523_ = v_isSharedCheck_554_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_extensions_519_);
lean_inc(v_defEqI_518_);
lean_inc(v_congrInfo_517_);
lean_inc(v_getLevel_516_);
lean_inc(v_inferType_515_);
lean_inc(v_proofInstInfo_514_);
lean_inc(v_maxFVar_513_);
lean_inc(v_share_512_);
lean_dec(v___x_511_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_554_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_524_; lean_object* v___x_526_; 
v___x_524_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2, &l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2_once, _init_l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2);
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 0, v___x_524_);
v___x_526_ = v___x_522_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v___x_524_);
lean_ctor_set(v_reuseFailAlloc_553_, 1, v_maxFVar_513_);
lean_ctor_set(v_reuseFailAlloc_553_, 2, v_proofInstInfo_514_);
lean_ctor_set(v_reuseFailAlloc_553_, 3, v_inferType_515_);
lean_ctor_set(v_reuseFailAlloc_553_, 4, v_getLevel_516_);
lean_ctor_set(v_reuseFailAlloc_553_, 5, v_congrInfo_517_);
lean_ctor_set(v_reuseFailAlloc_553_, 6, v_defEqI_518_);
lean_ctor_set(v_reuseFailAlloc_553_, 7, v_extensions_519_);
lean_ctor_set_uint8(v_reuseFailAlloc_553_, sizeof(void*)*8, v_debug_520_);
v___x_526_ = v_reuseFailAlloc_553_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
lean_object* v___x_527_; lean_object* v___x_528_; uint8_t v_debug_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v_fst_532_; lean_object* v_snd_533_; lean_object* v___x_534_; lean_object* v_maxFVar_535_; lean_object* v_proofInstInfo_536_; lean_object* v_inferType_537_; lean_object* v_getLevel_538_; lean_object* v_congrInfo_539_; lean_object* v_defEqI_540_; lean_object* v_extensions_541_; uint8_t v_debug_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_551_; 
v___x_527_ = lean_st_ref_set(v_a_505_, v___x_526_);
v___x_528_ = lean_st_ref_get(v_a_505_);
v_debug_529_ = lean_ctor_get_uint8(v___x_528_, sizeof(void*)*8);
lean_dec(v___x_528_);
v___x_530_ = lean_box(v_debug_529_);
v___x_531_ = lean_apply_2(v_k_503_, v___x_530_, v_share_512_);
v_fst_532_ = lean_ctor_get(v___x_531_, 0);
lean_inc(v_fst_532_);
v_snd_533_ = lean_ctor_get(v___x_531_, 1);
lean_inc(v_snd_533_);
lean_dec_ref(v___x_531_);
v___x_534_ = lean_st_ref_take(v_a_505_);
v_maxFVar_535_ = lean_ctor_get(v___x_534_, 1);
v_proofInstInfo_536_ = lean_ctor_get(v___x_534_, 2);
v_inferType_537_ = lean_ctor_get(v___x_534_, 3);
v_getLevel_538_ = lean_ctor_get(v___x_534_, 4);
v_congrInfo_539_ = lean_ctor_get(v___x_534_, 5);
v_defEqI_540_ = lean_ctor_get(v___x_534_, 6);
v_extensions_541_ = lean_ctor_get(v___x_534_, 7);
v_debug_542_ = lean_ctor_get_uint8(v___x_534_, sizeof(void*)*8);
v_isSharedCheck_551_ = !lean_is_exclusive(v___x_534_);
if (v_isSharedCheck_551_ == 0)
{
lean_object* v_unused_552_; 
v_unused_552_ = lean_ctor_get(v___x_534_, 0);
lean_dec(v_unused_552_);
v___x_544_ = v___x_534_;
v_isShared_545_ = v_isSharedCheck_551_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_extensions_541_);
lean_inc(v_defEqI_540_);
lean_inc(v_congrInfo_539_);
lean_inc(v_getLevel_538_);
lean_inc(v_inferType_537_);
lean_inc(v_proofInstInfo_536_);
lean_inc(v_maxFVar_535_);
lean_dec(v___x_534_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_551_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_547_; 
if (v_isShared_545_ == 0)
{
lean_ctor_set(v___x_544_, 0, v_snd_533_);
v___x_547_ = v___x_544_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_snd_533_);
lean_ctor_set(v_reuseFailAlloc_550_, 1, v_maxFVar_535_);
lean_ctor_set(v_reuseFailAlloc_550_, 2, v_proofInstInfo_536_);
lean_ctor_set(v_reuseFailAlloc_550_, 3, v_inferType_537_);
lean_ctor_set(v_reuseFailAlloc_550_, 4, v_getLevel_538_);
lean_ctor_set(v_reuseFailAlloc_550_, 5, v_congrInfo_539_);
lean_ctor_set(v_reuseFailAlloc_550_, 6, v_defEqI_540_);
lean_ctor_set(v_reuseFailAlloc_550_, 7, v_extensions_541_);
lean_ctor_set_uint8(v_reuseFailAlloc_550_, sizeof(void*)*8, v_debug_542_);
v___x_547_ = v_reuseFailAlloc_550_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_548_ = lean_st_ref_set(v_a_505_, v___x_547_);
v___x_549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_549_, 0, v_fst_532_);
return v___x_549_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM___boxed(lean_object* v_00_u03b1_555_, lean_object* v_k_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l_Lean_Meta_Sym_Internal_liftBuilderM(v_00_u03b1_555_, v_k_556_, v_a_557_, v_a_558_, v_a_559_, v_a_560_, v_a_561_, v_a_562_);
lean_dec(v_a_562_);
lean_dec_ref(v_a_561_);
lean_dec(v_a_560_);
lean_dec_ref(v_a_559_);
lean_dec(v_a_558_);
lean_dec_ref(v_a_557_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_share1___redArg(lean_object* v_e_565_, lean_object* v_a_566_){
_start:
{
lean_object* v___x_567_; uint64_t v___x_568_; size_t v___x_569_; lean_object* v___x_570_; uint8_t v___x_571_; 
v___x_567_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy;
v___x_568_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_565_);
v___x_569_ = lean_uint64_to_usize(v___x_568_);
lean_inc_ref(v_e_565_);
lean_inc_ref(v_a_566_);
v___x_570_ = l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg(v_a_566_, v___x_569_, v_e_565_, v___x_567_);
v___x_571_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_570_, v___x_567_);
if (v___x_571_ == 0)
{
lean_object* v___x_572_; 
lean_dec_ref(v_e_565_);
v___x_572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_572_, 0, v___x_570_);
lean_ctor_set(v___x_572_, 1, v_a_566_);
return v___x_572_;
}
else
{
lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
lean_dec_ref(v___x_570_);
v___x_573_ = lean_box(0);
lean_inc_ref(v_e_565_);
v___x_574_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1___redArg(v_a_566_, v_e_565_, v___x_573_);
v___x_575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_575_, 0, v_e_565_);
lean_ctor_set(v___x_575_, 1, v___x_574_);
return v___x_575_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_share1(lean_object* v_e_576_, uint8_t v_a_577_, lean_object* v_a_578_){
_start:
{
lean_object* v___x_579_; 
v___x_579_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v_e_576_, v_a_578_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_share1___boxed(lean_object* v_e_580_, lean_object* v_a_581_, lean_object* v_a_582_){
_start:
{
uint8_t v_a_boxed_583_; lean_object* v_res_584_; 
v_a_boxed_583_ = lean_unbox(v_a_581_);
v_res_584_ = l_Lean_Meta_Sym_Internal_Builder_share1(v_e_580_, v_a_boxed_583_, v_a_582_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1(lean_object* v_msg_592_, uint8_t v___y_593_, lean_object* v___y_594_){
_start:
{
lean_object* v___f_595_; lean_object* v___f_596_; lean_object* v___f_597_; lean_object* v___f_598_; lean_object* v___f_599_; lean_object* v___f_600_; lean_object* v___f_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___f_605_; lean_object* v___f_606_; lean_object* v___f_607_; lean_object* v___f_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___f_617_; lean_object* v___x_692__overap_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v___f_595_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__0));
v___f_596_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__1));
v___f_597_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__2));
v___f_598_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__3));
v___f_599_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__4));
v___f_600_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__5));
v___f_601_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__6));
v___x_602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_602_, 0, v___f_595_);
lean_ctor_set(v___x_602_, 1, v___f_596_);
v___x_603_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_603_, 0, v___x_602_);
lean_ctor_set(v___x_603_, 1, v___f_597_);
lean_ctor_set(v___x_603_, 2, v___f_598_);
lean_ctor_set(v___x_603_, 3, v___f_599_);
lean_ctor_set(v___x_603_, 4, v___f_600_);
v___x_604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_604_, 0, v___x_603_);
lean_ctor_set(v___x_604_, 1, v___f_601_);
lean_inc_ref(v___x_604_);
v___f_605_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_605_, 0, v___x_604_);
lean_inc_ref(v___x_604_);
v___f_606_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_606_, 0, v___x_604_);
lean_inc_ref(v___x_604_);
v___f_607_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_607_, 0, v___x_604_);
lean_inc_ref(v___x_604_);
v___f_608_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_608_, 0, v___x_604_);
lean_inc_ref(v___x_604_);
v___x_609_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_609_, 0, lean_box(0));
lean_closure_set(v___x_609_, 1, lean_box(0));
lean_closure_set(v___x_609_, 2, v___x_604_);
v___x_610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_610_, 0, v___x_609_);
lean_ctor_set(v___x_610_, 1, v___f_605_);
lean_inc_ref(v___x_604_);
v___x_611_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_611_, 0, lean_box(0));
lean_closure_set(v___x_611_, 1, lean_box(0));
lean_closure_set(v___x_611_, 2, v___x_604_);
v___x_612_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_612_, 0, v___x_610_);
lean_ctor_set(v___x_612_, 1, v___x_611_);
lean_ctor_set(v___x_612_, 2, v___f_606_);
lean_ctor_set(v___x_612_, 3, v___f_607_);
lean_ctor_set(v___x_612_, 4, v___f_608_);
v___x_613_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_613_, 0, lean_box(0));
lean_closure_set(v___x_613_, 1, lean_box(0));
lean_closure_set(v___x_613_, 2, v___x_604_);
v___x_614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_614_, 0, v___x_612_);
lean_ctor_set(v___x_614_, 1, v___x_613_);
v___x_615_ = lean_box(0);
v___x_616_ = l_instInhabitedOfMonad___redArg(v___x_614_, v___x_615_);
v___f_617_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_617_, 0, v___x_616_);
v___x_692__overap_618_ = lean_panic_fn(v___f_617_, v_msg_592_);
v___x_619_ = lean_box(v___y_593_);
v___x_620_ = lean_apply_2(v___x_692__overap_618_, v___x_619_, v___y_594_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___boxed(lean_object* v_msg_621_, lean_object* v___y_622_, lean_object* v___y_623_){
_start:
{
uint8_t v___y_825__boxed_624_; lean_object* v_res_625_; 
v___y_825__boxed_624_ = lean_unbox(v___y_622_);
v_res_625_ = l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1(v_msg_621_, v___y_825__boxed_624_, v___y_623_);
return v_res_625_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_626_, lean_object* v_i_627_, lean_object* v_k_628_){
_start:
{
lean_object* v___x_629_; uint8_t v___x_630_; 
v___x_629_ = lean_array_get_size(v_keys_626_);
v___x_630_ = lean_nat_dec_lt(v_i_627_, v___x_629_);
if (v___x_630_ == 0)
{
lean_dec_ref(v_k_628_);
lean_dec(v_i_627_);
return v___x_630_;
}
else
{
lean_object* v_k_x27_631_; uint8_t v___x_632_; 
v_k_x27_631_ = lean_array_fget_borrowed(v_keys_626_, v_i_627_);
lean_inc(v_k_x27_631_);
lean_inc_ref(v_k_628_);
v___x_632_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_k_628_, v_k_x27_631_);
if (v___x_632_ == 0)
{
lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_633_ = lean_unsigned_to_nat(1u);
v___x_634_ = lean_nat_add(v_i_627_, v___x_633_);
lean_dec(v_i_627_);
v_i_627_ = v___x_634_;
goto _start;
}
else
{
lean_dec_ref(v_k_628_);
lean_dec(v_i_627_);
return v___x_632_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_636_, lean_object* v_i_637_, lean_object* v_k_638_){
_start:
{
uint8_t v_res_639_; lean_object* v_r_640_; 
v_res_639_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg(v_keys_636_, v_i_637_, v_k_638_);
lean_dec_ref(v_keys_636_);
v_r_640_ = lean_box(v_res_639_);
return v_r_640_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg(lean_object* v_x_641_, size_t v_x_642_, lean_object* v_x_643_){
_start:
{
if (lean_obj_tag(v_x_641_) == 0)
{
lean_object* v_es_644_; lean_object* v___x_645_; size_t v___x_646_; size_t v___x_647_; size_t v___x_648_; lean_object* v_j_649_; lean_object* v___x_650_; 
v_es_644_ = lean_ctor_get(v_x_641_, 0);
lean_inc_ref(v_es_644_);
lean_dec_ref(v_x_641_);
v___x_645_ = lean_box(2);
v___x_646_ = ((size_t)5ULL);
v___x_647_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__1);
v___x_648_ = lean_usize_land(v_x_642_, v___x_647_);
v_j_649_ = lean_usize_to_nat(v___x_648_);
v___x_650_ = lean_array_get(v___x_645_, v_es_644_, v_j_649_);
lean_dec(v_j_649_);
lean_dec_ref(v_es_644_);
switch(lean_obj_tag(v___x_650_))
{
case 0:
{
lean_object* v_key_651_; uint8_t v___x_652_; 
v_key_651_ = lean_ctor_get(v___x_650_, 0);
lean_inc(v_key_651_);
lean_dec_ref(v___x_650_);
v___x_652_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_643_, v_key_651_);
return v___x_652_;
}
case 1:
{
lean_object* v_node_653_; size_t v___x_654_; 
v_node_653_ = lean_ctor_get(v___x_650_, 0);
lean_inc(v_node_653_);
lean_dec_ref(v___x_650_);
v___x_654_ = lean_usize_shift_right(v_x_642_, v___x_646_);
v_x_641_ = v_node_653_;
v_x_642_ = v___x_654_;
goto _start;
}
default: 
{
uint8_t v___x_656_; 
lean_dec_ref(v_x_643_);
v___x_656_ = 0;
return v___x_656_;
}
}
}
else
{
lean_object* v_ks_657_; lean_object* v___x_658_; uint8_t v___x_659_; 
v_ks_657_ = lean_ctor_get(v_x_641_, 0);
lean_inc_ref(v_ks_657_);
lean_dec_ref(v_x_641_);
v___x_658_ = lean_unsigned_to_nat(0u);
v___x_659_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg(v_ks_657_, v___x_658_, v_x_643_);
lean_dec_ref(v_ks_657_);
return v___x_659_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg___boxed(lean_object* v_x_660_, lean_object* v_x_661_, lean_object* v_x_662_){
_start:
{
size_t v_x_907__boxed_663_; uint8_t v_res_664_; lean_object* v_r_665_; 
v_x_907__boxed_663_ = lean_unbox_usize(v_x_661_);
lean_dec(v_x_661_);
v_res_664_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg(v_x_660_, v_x_907__boxed_663_, v_x_662_);
v_r_665_ = lean_box(v_res_664_);
return v_r_665_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg(lean_object* v_x_666_, lean_object* v_x_667_){
_start:
{
uint64_t v___x_668_; size_t v___x_669_; uint8_t v___x_670_; 
v___x_668_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_667_);
v___x_669_ = lean_uint64_to_usize(v___x_668_);
v___x_670_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg(v_x_666_, v___x_669_, v_x_667_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg___boxed(lean_object* v_x_671_, lean_object* v_x_672_){
_start:
{
uint8_t v_res_673_; lean_object* v_r_674_; 
v_res_673_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg(v_x_671_, v_x_672_);
v_r_674_ = lean_box(v_res_673_);
return v_r_674_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__2(void){
_start:
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_677_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__1));
v___x_678_ = lean_unsigned_to_nat(2u);
v___x_679_ = lean_unsigned_to_nat(74u);
v___x_680_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__0));
v___x_681_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_682_ = l_mkPanicMessageWithDecl(v___x_681_, v___x_680_, v___x_679_, v___x_678_, v___x_677_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_assertShared(lean_object* v_e_683_, uint8_t v_a_684_, lean_object* v_a_685_){
_start:
{
uint8_t v___x_686_; 
lean_inc_ref(v_a_685_);
v___x_686_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg(v_a_685_, v_e_683_);
if (v___x_686_ == 0)
{
lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_687_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__2, &l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__2_once, _init_l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__2);
v___x_688_ = l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1(v___x_687_, v_a_684_, v_a_685_);
return v___x_688_;
}
else
{
lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_689_ = lean_box(0);
v___x_690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_690_, 0, v___x_689_);
lean_ctor_set(v___x_690_, 1, v_a_685_);
return v___x_690_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_assertShared___boxed(lean_object* v_e_691_, lean_object* v_a_692_, lean_object* v_a_693_){
_start:
{
uint8_t v_a_boxed_694_; lean_object* v_res_695_; 
v_a_boxed_694_ = lean_unbox(v_a_692_);
v_res_695_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_e_691_, v_a_boxed_694_, v_a_693_);
return v_res_695_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0(lean_object* v_00_u03b2_696_, lean_object* v_x_697_, lean_object* v_x_698_){
_start:
{
uint8_t v___x_699_; 
v___x_699_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg(v_x_697_, v_x_698_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___boxed(lean_object* v_00_u03b2_700_, lean_object* v_x_701_, lean_object* v_x_702_){
_start:
{
uint8_t v_res_703_; lean_object* v_r_704_; 
v_res_703_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0(v_00_u03b2_700_, v_x_701_, v_x_702_);
v_r_704_ = lean_box(v_res_703_);
return v_r_704_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0(lean_object* v_00_u03b2_705_, lean_object* v_x_706_, size_t v_x_707_, lean_object* v_x_708_){
_start:
{
uint8_t v___x_709_; 
v___x_709_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg(v_x_706_, v_x_707_, v_x_708_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___boxed(lean_object* v_00_u03b2_710_, lean_object* v_x_711_, lean_object* v_x_712_, lean_object* v_x_713_){
_start:
{
size_t v_x_1008__boxed_714_; uint8_t v_res_715_; lean_object* v_r_716_; 
v_x_1008__boxed_714_ = lean_unbox_usize(v_x_712_);
lean_dec(v_x_712_);
v_res_715_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0(v_00_u03b2_710_, v_x_711_, v_x_1008__boxed_714_, v_x_713_);
v_r_716_ = lean_box(v_res_715_);
return v_r_716_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_717_, lean_object* v_keys_718_, lean_object* v_vals_719_, lean_object* v_heq_720_, lean_object* v_i_721_, lean_object* v_k_722_){
_start:
{
uint8_t v___x_723_; 
v___x_723_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg(v_keys_718_, v_i_721_, v_k_722_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_724_, lean_object* v_keys_725_, lean_object* v_vals_726_, lean_object* v_heq_727_, lean_object* v_i_728_, lean_object* v_k_729_){
_start:
{
uint8_t v_res_730_; lean_object* v_r_731_; 
v_res_730_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2(v_00_u03b2_724_, v_keys_725_, v_vals_726_, v_heq_727_, v_i_728_, v_k_729_);
lean_dec_ref(v_vals_726_);
lean_dec_ref(v_keys_725_);
v_r_731_ = lean_box(v_res_730_);
return v_r_731_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM(void){
_start:
{
lean_object* v___f_734_; lean_object* v___f_735_; lean_object* v___f_736_; lean_object* v___f_737_; lean_object* v___f_738_; lean_object* v___f_739_; lean_object* v___f_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___f_744_; lean_object* v___f_745_; lean_object* v___f_746_; lean_object* v___f_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; 
v___f_734_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__0));
v___f_735_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__1));
v___f_736_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__2));
v___f_737_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__3));
v___f_738_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__4));
v___f_739_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__5));
v___f_740_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__6));
v___x_741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_741_, 0, v___f_734_);
lean_ctor_set(v___x_741_, 1, v___f_735_);
v___x_742_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_742_, 0, v___x_741_);
lean_ctor_set(v___x_742_, 1, v___f_736_);
lean_ctor_set(v___x_742_, 2, v___f_737_);
lean_ctor_set(v___x_742_, 3, v___f_738_);
lean_ctor_set(v___x_742_, 4, v___f_739_);
v___x_743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_743_, 0, v___x_742_);
lean_ctor_set(v___x_743_, 1, v___f_740_);
lean_inc_ref(v___x_743_);
v___f_744_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_744_, 0, v___x_743_);
lean_inc_ref(v___x_743_);
v___f_745_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_745_, 0, v___x_743_);
lean_inc_ref(v___x_743_);
v___f_746_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_746_, 0, v___x_743_);
lean_inc_ref(v___x_743_);
v___f_747_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_747_, 0, v___x_743_);
lean_inc_ref(v___x_743_);
v___x_748_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_748_, 0, lean_box(0));
lean_closure_set(v___x_748_, 1, lean_box(0));
lean_closure_set(v___x_748_, 2, v___x_743_);
v___x_749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_749_, 0, v___x_748_);
lean_ctor_set(v___x_749_, 1, v___f_744_);
lean_inc_ref(v___x_743_);
v___x_750_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_750_, 0, lean_box(0));
lean_closure_set(v___x_750_, 1, lean_box(0));
lean_closure_set(v___x_750_, 2, v___x_743_);
v___x_751_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_751_, 0, v___x_749_);
lean_ctor_set(v___x_751_, 1, v___x_750_);
lean_ctor_set(v___x_751_, 2, v___f_745_);
lean_ctor_set(v___x_751_, 3, v___f_746_);
lean_ctor_set(v___x_751_, 4, v___f_747_);
v___x_752_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_752_, 0, lean_box(0));
lean_closure_set(v___x_752_, 1, lean_box(0));
lean_closure_set(v___x_752_, 2, v___x_743_);
v___x_753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_753_, 0, v___x_751_);
lean_ctor_set(v___x_753_, 1, v___x_752_);
v___x_754_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__0));
v___x_755_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__1));
v___x_756_ = lean_alloc_closure((void*)(l_ReaderT_read___boxed), 4, 3);
lean_closure_set(v___x_756_, 0, lean_box(0));
lean_closure_set(v___x_756_, 1, lean_box(0));
lean_closure_set(v___x_756_, 2, v___x_753_);
v___x_757_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_757_, 0, v___x_754_);
lean_ctor_set(v___x_757_, 1, v___x_755_);
lean_ctor_set(v___x_757_, 2, v___x_756_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLitS___redArg(lean_object* v_inst_758_, lean_object* v_l_759_){
_start:
{
lean_object* v_share1_760_; lean_object* v___x_761_; lean_object* v___x_762_; 
v_share1_760_ = lean_ctor_get(v_inst_758_, 0);
lean_inc(v_share1_760_);
lean_dec_ref(v_inst_758_);
v___x_761_ = l_Lean_Expr_lit___override(v_l_759_);
v___x_762_ = lean_apply_1(v_share1_760_, v___x_761_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLitS(lean_object* v_m_763_, lean_object* v_inst_764_, lean_object* v_l_765_){
_start:
{
lean_object* v___x_766_; 
v___x_766_ = l_Lean_Meta_Sym_Internal_mkLitS___redArg(v_inst_764_, v_l_765_);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___redArg(lean_object* v_inst_767_, lean_object* v_declName_768_, lean_object* v_us_769_){
_start:
{
lean_object* v_share1_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
v_share1_770_ = lean_ctor_get(v_inst_767_, 0);
lean_inc(v_share1_770_);
lean_dec_ref(v_inst_767_);
v___x_771_ = l_Lean_Expr_const___override(v_declName_768_, v_us_769_);
v___x_772_ = lean_apply_1(v_share1_770_, v___x_771_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS(lean_object* v_m_773_, lean_object* v_inst_774_, lean_object* v_declName_775_, lean_object* v_us_776_){
_start:
{
lean_object* v___x_777_; 
v___x_777_ = l_Lean_Meta_Sym_Internal_mkConstS___redArg(v_inst_774_, v_declName_775_, v_us_776_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___redArg(lean_object* v_inst_778_, lean_object* v_idx_779_){
_start:
{
lean_object* v_share1_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
v_share1_780_ = lean_ctor_get(v_inst_778_, 0);
lean_inc(v_share1_780_);
lean_dec_ref(v_inst_778_);
v___x_781_ = l_Lean_Expr_bvar___override(v_idx_779_);
v___x_782_ = lean_apply_1(v_share1_780_, v___x_781_);
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS(lean_object* v_m_783_, lean_object* v_inst_784_, lean_object* v_idx_785_){
_start:
{
lean_object* v___x_786_; 
v___x_786_ = l_Lean_Meta_Sym_Internal_mkBVarS___redArg(v_inst_784_, v_idx_785_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS___redArg(lean_object* v_inst_787_, lean_object* v_u_788_){
_start:
{
lean_object* v_share1_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
v_share1_789_ = lean_ctor_get(v_inst_787_, 0);
lean_inc(v_share1_789_);
lean_dec_ref(v_inst_787_);
v___x_790_ = l_Lean_Expr_sort___override(v_u_788_);
v___x_791_ = lean_apply_1(v_share1_789_, v___x_790_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS(lean_object* v_m_792_, lean_object* v_inst_793_, lean_object* v_u_794_){
_start:
{
lean_object* v___x_795_; 
v___x_795_ = l_Lean_Meta_Sym_Internal_mkSortS___redArg(v_inst_793_, v_u_794_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___redArg(lean_object* v_inst_796_, lean_object* v_fvarId_797_){
_start:
{
lean_object* v_share1_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
v_share1_798_ = lean_ctor_get(v_inst_796_, 0);
lean_inc(v_share1_798_);
lean_dec_ref(v_inst_796_);
v___x_799_ = l_Lean_Expr_fvar___override(v_fvarId_797_);
v___x_800_ = lean_apply_1(v_share1_798_, v___x_799_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS(lean_object* v_m_801_, lean_object* v_inst_802_, lean_object* v_fvarId_803_){
_start:
{
lean_object* v___x_804_; 
v___x_804_ = l_Lean_Meta_Sym_Internal_mkFVarS___redArg(v_inst_802_, v_fvarId_803_);
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMVarS___redArg(lean_object* v_inst_805_, lean_object* v_mvarId_806_){
_start:
{
lean_object* v_share1_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
v_share1_807_ = lean_ctor_get(v_inst_805_, 0);
lean_inc(v_share1_807_);
lean_dec_ref(v_inst_805_);
v___x_808_ = l_Lean_Expr_mvar___override(v_mvarId_806_);
v___x_809_ = lean_apply_1(v_share1_807_, v___x_808_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMVarS(lean_object* v_m_810_, lean_object* v_inst_811_, lean_object* v_mvarId_812_){
_start:
{
lean_object* v___x_813_; 
v___x_813_ = l_Lean_Meta_Sym_Internal_mkMVarS___redArg(v_inst_811_, v_mvarId_812_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__0(lean_object* v_d_814_, lean_object* v_e_815_, lean_object* v_share1_816_, lean_object* v_____r_817_){
_start:
{
lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_818_ = l_Lean_Expr_mdata___override(v_d_814_, v_e_815_);
v___x_819_ = lean_apply_1(v_share1_816_, v___x_818_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1(lean_object* v___f_820_, lean_object* v_____r_821_){
_start:
{
lean_object* v___x_822_; 
v___x_822_ = lean_apply_1(v___f_820_, v_____r_821_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__2(lean_object* v___f_823_, lean_object* v_assertShared_824_, lean_object* v_e_825_, lean_object* v_toBind_826_, lean_object* v___f_827_, uint8_t v_____do__lift_828_){
_start:
{
if (v_____do__lift_828_ == 0)
{
lean_object* v___x_829_; lean_object* v___x_830_; 
lean_dec(v___f_827_);
lean_dec(v_toBind_826_);
lean_dec_ref(v_e_825_);
lean_dec(v_assertShared_824_);
v___x_829_ = lean_box(0);
v___x_830_ = lean_apply_1(v___f_823_, v___x_829_);
return v___x_830_;
}
else
{
lean_object* v___x_831_; lean_object* v___x_832_; 
lean_dec(v___f_823_);
v___x_831_ = lean_apply_1(v_assertShared_824_, v_e_825_);
v___x_832_ = lean_apply_4(v_toBind_826_, lean_box(0), lean_box(0), v___x_831_, v___f_827_);
return v___x_832_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__2___boxed(lean_object* v___f_833_, lean_object* v_assertShared_834_, lean_object* v_e_835_, lean_object* v_toBind_836_, lean_object* v___f_837_, lean_object* v_____do__lift_838_){
_start:
{
uint8_t v_____do__lift_85__boxed_839_; lean_object* v_res_840_; 
v_____do__lift_85__boxed_839_ = lean_unbox(v_____do__lift_838_);
v_res_840_ = l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__2(v___f_833_, v_assertShared_834_, v_e_835_, v_toBind_836_, v___f_837_, v_____do__lift_85__boxed_839_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg(lean_object* v_inst_841_, lean_object* v_inst_842_, lean_object* v_d_843_, lean_object* v_e_844_){
_start:
{
lean_object* v_toBind_845_; lean_object* v_share1_846_; lean_object* v_assertShared_847_; lean_object* v_isDebugEnabled_848_; lean_object* v___f_849_; lean_object* v___f_850_; lean_object* v___f_851_; lean_object* v___x_852_; 
v_toBind_845_ = lean_ctor_get(v_inst_842_, 1);
lean_inc(v_toBind_845_);
lean_dec_ref(v_inst_842_);
v_share1_846_ = lean_ctor_get(v_inst_841_, 0);
lean_inc(v_share1_846_);
v_assertShared_847_ = lean_ctor_get(v_inst_841_, 1);
lean_inc(v_assertShared_847_);
v_isDebugEnabled_848_ = lean_ctor_get(v_inst_841_, 2);
lean_inc(v_isDebugEnabled_848_);
lean_dec_ref(v_inst_841_);
lean_inc_ref(v_e_844_);
v___f_849_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__0), 4, 3);
lean_closure_set(v___f_849_, 0, v_d_843_);
lean_closure_set(v___f_849_, 1, v_e_844_);
lean_closure_set(v___f_849_, 2, v_share1_846_);
lean_inc_ref(v___f_849_);
v___f_850_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_850_, 0, v___f_849_);
lean_inc(v_toBind_845_);
v___f_851_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_851_, 0, v___f_849_);
lean_closure_set(v___f_851_, 1, v_assertShared_847_);
lean_closure_set(v___f_851_, 2, v_e_844_);
lean_closure_set(v___f_851_, 3, v_toBind_845_);
lean_closure_set(v___f_851_, 4, v___f_850_);
v___x_852_ = lean_apply_4(v_toBind_845_, lean_box(0), lean_box(0), v_isDebugEnabled_848_, v___f_851_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS(lean_object* v_m_853_, lean_object* v_inst_854_, lean_object* v_inst_855_, lean_object* v_d_856_, lean_object* v_e_857_){
_start:
{
lean_object* v___x_858_; 
v___x_858_ = l_Lean_Meta_Sym_Internal_mkMDataS___redArg(v_inst_854_, v_inst_855_, v_d_856_, v_e_857_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__0(lean_object* v_structName_859_, lean_object* v_idx_860_, lean_object* v_struct_861_, lean_object* v_share1_862_, lean_object* v_____r_863_){
_start:
{
lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_864_ = l_Lean_Expr_proj___override(v_structName_859_, v_idx_860_, v_struct_861_);
v___x_865_ = lean_apply_1(v_share1_862_, v___x_864_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__2(lean_object* v___f_866_, lean_object* v_assertShared_867_, lean_object* v_struct_868_, lean_object* v_toBind_869_, lean_object* v___f_870_, uint8_t v_____do__lift_871_){
_start:
{
if (v_____do__lift_871_ == 0)
{
lean_object* v___x_872_; lean_object* v___x_873_; 
lean_dec(v___f_870_);
lean_dec(v_toBind_869_);
lean_dec_ref(v_struct_868_);
lean_dec(v_assertShared_867_);
v___x_872_ = lean_box(0);
v___x_873_ = lean_apply_1(v___f_866_, v___x_872_);
return v___x_873_;
}
else
{
lean_object* v___x_874_; lean_object* v___x_875_; 
lean_dec(v___f_866_);
v___x_874_ = lean_apply_1(v_assertShared_867_, v_struct_868_);
v___x_875_ = lean_apply_4(v_toBind_869_, lean_box(0), lean_box(0), v___x_874_, v___f_870_);
return v___x_875_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__2___boxed(lean_object* v___f_876_, lean_object* v_assertShared_877_, lean_object* v_struct_878_, lean_object* v_toBind_879_, lean_object* v___f_880_, lean_object* v_____do__lift_881_){
_start:
{
uint8_t v_____do__lift_79__boxed_882_; lean_object* v_res_883_; 
v_____do__lift_79__boxed_882_ = lean_unbox(v_____do__lift_881_);
v_res_883_ = l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__2(v___f_876_, v_assertShared_877_, v_struct_878_, v_toBind_879_, v___f_880_, v_____do__lift_79__boxed_882_);
return v_res_883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___redArg(lean_object* v_inst_884_, lean_object* v_inst_885_, lean_object* v_structName_886_, lean_object* v_idx_887_, lean_object* v_struct_888_){
_start:
{
lean_object* v_toBind_889_; lean_object* v_share1_890_; lean_object* v_assertShared_891_; lean_object* v_isDebugEnabled_892_; lean_object* v___f_893_; lean_object* v___f_894_; lean_object* v___f_895_; lean_object* v___x_896_; 
v_toBind_889_ = lean_ctor_get(v_inst_885_, 1);
lean_inc(v_toBind_889_);
lean_dec_ref(v_inst_885_);
v_share1_890_ = lean_ctor_get(v_inst_884_, 0);
lean_inc(v_share1_890_);
v_assertShared_891_ = lean_ctor_get(v_inst_884_, 1);
lean_inc(v_assertShared_891_);
v_isDebugEnabled_892_ = lean_ctor_get(v_inst_884_, 2);
lean_inc(v_isDebugEnabled_892_);
lean_dec_ref(v_inst_884_);
lean_inc_ref(v_struct_888_);
v___f_893_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__0), 5, 4);
lean_closure_set(v___f_893_, 0, v_structName_886_);
lean_closure_set(v___f_893_, 1, v_idx_887_);
lean_closure_set(v___f_893_, 2, v_struct_888_);
lean_closure_set(v___f_893_, 3, v_share1_890_);
lean_inc_ref(v___f_893_);
v___f_894_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_894_, 0, v___f_893_);
lean_inc(v_toBind_889_);
v___f_895_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_895_, 0, v___f_893_);
lean_closure_set(v___f_895_, 1, v_assertShared_891_);
lean_closure_set(v___f_895_, 2, v_struct_888_);
lean_closure_set(v___f_895_, 3, v_toBind_889_);
lean_closure_set(v___f_895_, 4, v___f_894_);
v___x_896_ = lean_apply_4(v_toBind_889_, lean_box(0), lean_box(0), v_isDebugEnabled_892_, v___f_895_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS(lean_object* v_m_897_, lean_object* v_inst_898_, lean_object* v_inst_899_, lean_object* v_structName_900_, lean_object* v_idx_901_, lean_object* v_struct_902_){
_start:
{
lean_object* v___x_903_; 
v___x_903_ = l_Lean_Meta_Sym_Internal_mkProjS___redArg(v_inst_898_, v_inst_899_, v_structName_900_, v_idx_901_, v_struct_902_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__0(lean_object* v_f_904_, lean_object* v_a_905_, lean_object* v_share1_906_, lean_object* v_____r_907_){
_start:
{
lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_908_ = l_Lean_Expr_app___override(v_f_904_, v_a_905_);
v___x_909_ = lean_apply_1(v_share1_906_, v___x_908_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__2(lean_object* v_assertShared_910_, lean_object* v_a_911_, lean_object* v_toBind_912_, lean_object* v___f_913_, lean_object* v_____r_914_){
_start:
{
lean_object* v___x_915_; lean_object* v___x_916_; 
v___x_915_ = lean_apply_1(v_assertShared_910_, v_a_911_);
v___x_916_ = lean_apply_4(v_toBind_912_, lean_box(0), lean_box(0), v___x_915_, v___f_913_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__1(lean_object* v___f_917_, lean_object* v_assertShared_918_, lean_object* v_a_919_, lean_object* v_toBind_920_, lean_object* v___f_921_, lean_object* v_f_922_, uint8_t v_____do__lift_923_){
_start:
{
if (v_____do__lift_923_ == 0)
{
lean_object* v___x_924_; lean_object* v___x_925_; 
lean_dec_ref(v_f_922_);
lean_dec(v___f_921_);
lean_dec(v_toBind_920_);
lean_dec_ref(v_a_919_);
lean_dec(v_assertShared_918_);
v___x_924_ = lean_box(0);
v___x_925_ = lean_apply_1(v___f_917_, v___x_924_);
return v___x_925_;
}
else
{
lean_object* v___f_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
lean_dec(v___f_917_);
lean_inc(v_toBind_920_);
lean_inc(v_assertShared_918_);
v___f_926_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__2), 5, 4);
lean_closure_set(v___f_926_, 0, v_assertShared_918_);
lean_closure_set(v___f_926_, 1, v_a_919_);
lean_closure_set(v___f_926_, 2, v_toBind_920_);
lean_closure_set(v___f_926_, 3, v___f_921_);
v___x_927_ = lean_apply_1(v_assertShared_918_, v_f_922_);
v___x_928_ = lean_apply_4(v_toBind_920_, lean_box(0), lean_box(0), v___x_927_, v___f_926_);
return v___x_928_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__1___boxed(lean_object* v___f_929_, lean_object* v_assertShared_930_, lean_object* v_a_931_, lean_object* v_toBind_932_, lean_object* v___f_933_, lean_object* v_f_934_, lean_object* v_____do__lift_935_){
_start:
{
uint8_t v_____do__lift_104__boxed_936_; lean_object* v_res_937_; 
v_____do__lift_104__boxed_936_ = lean_unbox(v_____do__lift_935_);
v_res_937_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__1(v___f_929_, v_assertShared_930_, v_a_931_, v_toBind_932_, v___f_933_, v_f_934_, v_____do__lift_104__boxed_936_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg(lean_object* v_inst_938_, lean_object* v_inst_939_, lean_object* v_f_940_, lean_object* v_a_941_){
_start:
{
lean_object* v_toBind_942_; lean_object* v_share1_943_; lean_object* v_assertShared_944_; lean_object* v_isDebugEnabled_945_; lean_object* v___f_946_; lean_object* v___f_947_; lean_object* v___f_948_; lean_object* v___x_949_; 
v_toBind_942_ = lean_ctor_get(v_inst_939_, 1);
lean_inc(v_toBind_942_);
lean_dec_ref(v_inst_939_);
v_share1_943_ = lean_ctor_get(v_inst_938_, 0);
lean_inc(v_share1_943_);
v_assertShared_944_ = lean_ctor_get(v_inst_938_, 1);
lean_inc(v_assertShared_944_);
v_isDebugEnabled_945_ = lean_ctor_get(v_inst_938_, 2);
lean_inc(v_isDebugEnabled_945_);
lean_dec_ref(v_inst_938_);
lean_inc_ref(v_a_941_);
lean_inc_ref(v_f_940_);
v___f_946_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__0), 4, 3);
lean_closure_set(v___f_946_, 0, v_f_940_);
lean_closure_set(v___f_946_, 1, v_a_941_);
lean_closure_set(v___f_946_, 2, v_share1_943_);
lean_inc_ref(v___f_946_);
v___f_947_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_947_, 0, v___f_946_);
lean_inc(v_toBind_942_);
v___f_948_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_948_, 0, v___f_946_);
lean_closure_set(v___f_948_, 1, v_assertShared_944_);
lean_closure_set(v___f_948_, 2, v_a_941_);
lean_closure_set(v___f_948_, 3, v_toBind_942_);
lean_closure_set(v___f_948_, 4, v___f_947_);
lean_closure_set(v___f_948_, 5, v_f_940_);
v___x_949_ = lean_apply_4(v_toBind_942_, lean_box(0), lean_box(0), v_isDebugEnabled_945_, v___f_948_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS(lean_object* v_m_950_, lean_object* v_inst_951_, lean_object* v_inst_952_, lean_object* v_f_953_, lean_object* v_a_954_){
_start:
{
lean_object* v___x_955_; 
v___x_955_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_951_, v_inst_952_, v_f_953_, v_a_954_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__0(lean_object* v_x_956_, lean_object* v_t_957_, lean_object* v_b_958_, uint8_t v_bi_959_, lean_object* v_share1_960_, lean_object* v_____r_961_){
_start:
{
lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_962_ = l_Lean_Expr_lam___override(v_x_956_, v_t_957_, v_b_958_, v_bi_959_);
v___x_963_ = lean_apply_1(v_share1_960_, v___x_962_);
return v___x_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__0___boxed(lean_object* v_x_964_, lean_object* v_t_965_, lean_object* v_b_966_, lean_object* v_bi_967_, lean_object* v_share1_968_, lean_object* v_____r_969_){
_start:
{
uint8_t v_bi_boxed_970_; lean_object* v_res_971_; 
v_bi_boxed_970_ = lean_unbox(v_bi_967_);
v_res_971_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__0(v_x_964_, v_t_965_, v_b_966_, v_bi_boxed_970_, v_share1_968_, v_____r_969_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__2(lean_object* v_assertShared_972_, lean_object* v_b_973_, lean_object* v_toBind_974_, lean_object* v___f_975_, lean_object* v_____r_976_){
_start:
{
lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_977_ = lean_apply_1(v_assertShared_972_, v_b_973_);
v___x_978_ = lean_apply_4(v_toBind_974_, lean_box(0), lean_box(0), v___x_977_, v___f_975_);
return v___x_978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1(lean_object* v___f_979_, lean_object* v_assertShared_980_, lean_object* v_b_981_, lean_object* v_toBind_982_, lean_object* v___f_983_, lean_object* v_t_984_, uint8_t v_____do__lift_985_){
_start:
{
if (v_____do__lift_985_ == 0)
{
lean_object* v___x_986_; lean_object* v___x_987_; 
lean_dec_ref(v_t_984_);
lean_dec(v___f_983_);
lean_dec(v_toBind_982_);
lean_dec_ref(v_b_981_);
lean_dec(v_assertShared_980_);
v___x_986_ = lean_box(0);
v___x_987_ = lean_apply_1(v___f_979_, v___x_986_);
return v___x_987_;
}
else
{
lean_object* v___f_988_; lean_object* v___x_989_; lean_object* v___x_990_; 
lean_dec(v___f_979_);
lean_inc(v_toBind_982_);
lean_inc(v_assertShared_980_);
v___f_988_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__2), 5, 4);
lean_closure_set(v___f_988_, 0, v_assertShared_980_);
lean_closure_set(v___f_988_, 1, v_b_981_);
lean_closure_set(v___f_988_, 2, v_toBind_982_);
lean_closure_set(v___f_988_, 3, v___f_983_);
v___x_989_ = lean_apply_1(v_assertShared_980_, v_t_984_);
v___x_990_ = lean_apply_4(v_toBind_982_, lean_box(0), lean_box(0), v___x_989_, v___f_988_);
return v___x_990_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1___boxed(lean_object* v___f_991_, lean_object* v_assertShared_992_, lean_object* v_b_993_, lean_object* v_toBind_994_, lean_object* v___f_995_, lean_object* v_t_996_, lean_object* v_____do__lift_997_){
_start:
{
uint8_t v_____do__lift_105__boxed_998_; lean_object* v_res_999_; 
v_____do__lift_105__boxed_998_ = lean_unbox(v_____do__lift_997_);
v_res_999_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1(v___f_991_, v_assertShared_992_, v_b_993_, v_toBind_994_, v___f_995_, v_t_996_, v_____do__lift_105__boxed_998_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(lean_object* v_inst_1000_, lean_object* v_inst_1001_, lean_object* v_x_1002_, uint8_t v_bi_1003_, lean_object* v_t_1004_, lean_object* v_b_1005_){
_start:
{
lean_object* v_toBind_1006_; lean_object* v_share1_1007_; lean_object* v_assertShared_1008_; lean_object* v_isDebugEnabled_1009_; lean_object* v___x_1010_; lean_object* v___f_1011_; lean_object* v___f_1012_; lean_object* v___f_1013_; lean_object* v___x_1014_; 
v_toBind_1006_ = lean_ctor_get(v_inst_1001_, 1);
lean_inc(v_toBind_1006_);
lean_dec_ref(v_inst_1001_);
v_share1_1007_ = lean_ctor_get(v_inst_1000_, 0);
lean_inc(v_share1_1007_);
v_assertShared_1008_ = lean_ctor_get(v_inst_1000_, 1);
lean_inc(v_assertShared_1008_);
v_isDebugEnabled_1009_ = lean_ctor_get(v_inst_1000_, 2);
lean_inc(v_isDebugEnabled_1009_);
lean_dec_ref(v_inst_1000_);
v___x_1010_ = lean_box(v_bi_1003_);
lean_inc_ref(v_b_1005_);
lean_inc_ref(v_t_1004_);
v___f_1011_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1011_, 0, v_x_1002_);
lean_closure_set(v___f_1011_, 1, v_t_1004_);
lean_closure_set(v___f_1011_, 2, v_b_1005_);
lean_closure_set(v___f_1011_, 3, v___x_1010_);
lean_closure_set(v___f_1011_, 4, v_share1_1007_);
lean_inc_ref(v___f_1011_);
v___f_1012_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1012_, 0, v___f_1011_);
lean_inc(v_toBind_1006_);
v___f_1013_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_1013_, 0, v___f_1011_);
lean_closure_set(v___f_1013_, 1, v_assertShared_1008_);
lean_closure_set(v___f_1013_, 2, v_b_1005_);
lean_closure_set(v___f_1013_, 3, v_toBind_1006_);
lean_closure_set(v___f_1013_, 4, v___f_1012_);
lean_closure_set(v___f_1013_, 5, v_t_1004_);
v___x_1014_ = lean_apply_4(v_toBind_1006_, lean_box(0), lean_box(0), v_isDebugEnabled_1009_, v___f_1013_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___boxed(lean_object* v_inst_1015_, lean_object* v_inst_1016_, lean_object* v_x_1017_, lean_object* v_bi_1018_, lean_object* v_t_1019_, lean_object* v_b_1020_){
_start:
{
uint8_t v_bi_boxed_1021_; lean_object* v_res_1022_; 
v_bi_boxed_1021_ = lean_unbox(v_bi_1018_);
v_res_1022_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v_inst_1015_, v_inst_1016_, v_x_1017_, v_bi_boxed_1021_, v_t_1019_, v_b_1020_);
return v_res_1022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS(lean_object* v_m_1023_, lean_object* v_inst_1024_, lean_object* v_inst_1025_, lean_object* v_x_1026_, uint8_t v_bi_1027_, lean_object* v_t_1028_, lean_object* v_b_1029_){
_start:
{
lean_object* v___x_1030_; 
v___x_1030_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v_inst_1024_, v_inst_1025_, v_x_1026_, v_bi_1027_, v_t_1028_, v_b_1029_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___boxed(lean_object* v_m_1031_, lean_object* v_inst_1032_, lean_object* v_inst_1033_, lean_object* v_x_1034_, lean_object* v_bi_1035_, lean_object* v_t_1036_, lean_object* v_b_1037_){
_start:
{
uint8_t v_bi_boxed_1038_; lean_object* v_res_1039_; 
v_bi_boxed_1038_ = lean_unbox(v_bi_1035_);
v_res_1039_ = l_Lean_Meta_Sym_Internal_mkLambdaS(v_m_1031_, v_inst_1032_, v_inst_1033_, v_x_1034_, v_bi_boxed_1038_, v_t_1036_, v_b_1037_);
return v_res_1039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___redArg___lam__0(lean_object* v_x_1040_, lean_object* v_t_1041_, lean_object* v_b_1042_, uint8_t v_bi_1043_, lean_object* v_share1_1044_, lean_object* v_____r_1045_){
_start:
{
lean_object* v___x_1046_; lean_object* v___x_1047_; 
v___x_1046_ = l_Lean_Expr_forallE___override(v_x_1040_, v_t_1041_, v_b_1042_, v_bi_1043_);
v___x_1047_ = lean_apply_1(v_share1_1044_, v___x_1046_);
return v___x_1047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___redArg___lam__0___boxed(lean_object* v_x_1048_, lean_object* v_t_1049_, lean_object* v_b_1050_, lean_object* v_bi_1051_, lean_object* v_share1_1052_, lean_object* v_____r_1053_){
_start:
{
uint8_t v_bi_boxed_1054_; lean_object* v_res_1055_; 
v_bi_boxed_1054_ = lean_unbox(v_bi_1051_);
v_res_1055_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg___lam__0(v_x_1048_, v_t_1049_, v_b_1050_, v_bi_boxed_1054_, v_share1_1052_, v_____r_1053_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___redArg(lean_object* v_inst_1056_, lean_object* v_inst_1057_, lean_object* v_x_1058_, uint8_t v_bi_1059_, lean_object* v_t_1060_, lean_object* v_b_1061_){
_start:
{
lean_object* v_toBind_1062_; lean_object* v_share1_1063_; lean_object* v_assertShared_1064_; lean_object* v_isDebugEnabled_1065_; lean_object* v___x_1066_; lean_object* v___f_1067_; lean_object* v___f_1068_; lean_object* v___f_1069_; lean_object* v___x_1070_; 
v_toBind_1062_ = lean_ctor_get(v_inst_1057_, 1);
lean_inc(v_toBind_1062_);
lean_dec_ref(v_inst_1057_);
v_share1_1063_ = lean_ctor_get(v_inst_1056_, 0);
lean_inc(v_share1_1063_);
v_assertShared_1064_ = lean_ctor_get(v_inst_1056_, 1);
lean_inc(v_assertShared_1064_);
v_isDebugEnabled_1065_ = lean_ctor_get(v_inst_1056_, 2);
lean_inc(v_isDebugEnabled_1065_);
lean_dec_ref(v_inst_1056_);
v___x_1066_ = lean_box(v_bi_1059_);
lean_inc_ref(v_b_1061_);
lean_inc_ref(v_t_1060_);
v___f_1067_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkForallS___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1067_, 0, v_x_1058_);
lean_closure_set(v___f_1067_, 1, v_t_1060_);
lean_closure_set(v___f_1067_, 2, v_b_1061_);
lean_closure_set(v___f_1067_, 3, v___x_1066_);
lean_closure_set(v___f_1067_, 4, v_share1_1063_);
lean_inc_ref(v___f_1067_);
v___f_1068_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1068_, 0, v___f_1067_);
lean_inc(v_toBind_1062_);
v___f_1069_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_1069_, 0, v___f_1067_);
lean_closure_set(v___f_1069_, 1, v_assertShared_1064_);
lean_closure_set(v___f_1069_, 2, v_b_1061_);
lean_closure_set(v___f_1069_, 3, v_toBind_1062_);
lean_closure_set(v___f_1069_, 4, v___f_1068_);
lean_closure_set(v___f_1069_, 5, v_t_1060_);
v___x_1070_ = lean_apply_4(v_toBind_1062_, lean_box(0), lean_box(0), v_isDebugEnabled_1065_, v___f_1069_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___redArg___boxed(lean_object* v_inst_1071_, lean_object* v_inst_1072_, lean_object* v_x_1073_, lean_object* v_bi_1074_, lean_object* v_t_1075_, lean_object* v_b_1076_){
_start:
{
uint8_t v_bi_boxed_1077_; lean_object* v_res_1078_; 
v_bi_boxed_1077_ = lean_unbox(v_bi_1074_);
v_res_1078_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v_inst_1071_, v_inst_1072_, v_x_1073_, v_bi_boxed_1077_, v_t_1075_, v_b_1076_);
return v_res_1078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS(lean_object* v_m_1079_, lean_object* v_inst_1080_, lean_object* v_inst_1081_, lean_object* v_x_1082_, uint8_t v_bi_1083_, lean_object* v_t_1084_, lean_object* v_b_1085_){
_start:
{
lean_object* v___x_1086_; 
v___x_1086_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v_inst_1080_, v_inst_1081_, v_x_1082_, v_bi_1083_, v_t_1084_, v_b_1085_);
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___boxed(lean_object* v_m_1087_, lean_object* v_inst_1088_, lean_object* v_inst_1089_, lean_object* v_x_1090_, lean_object* v_bi_1091_, lean_object* v_t_1092_, lean_object* v_b_1093_){
_start:
{
uint8_t v_bi_boxed_1094_; lean_object* v_res_1095_; 
v_bi_boxed_1094_ = lean_unbox(v_bi_1091_);
v_res_1095_ = l_Lean_Meta_Sym_Internal_mkForallS(v_m_1087_, v_inst_1088_, v_inst_1089_, v_x_1090_, v_bi_boxed_1094_, v_t_1092_, v_b_1093_);
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__0(lean_object* v_x_1096_, lean_object* v_t_1097_, lean_object* v_v_1098_, lean_object* v_b_1099_, uint8_t v_nondep_1100_, lean_object* v_share1_1101_, lean_object* v_____r_1102_){
_start:
{
lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1103_ = l_Lean_Expr_letE___override(v_x_1096_, v_t_1097_, v_v_1098_, v_b_1099_, v_nondep_1100_);
v___x_1104_ = lean_apply_1(v_share1_1101_, v___x_1103_);
return v___x_1104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__0___boxed(lean_object* v_x_1105_, lean_object* v_t_1106_, lean_object* v_v_1107_, lean_object* v_b_1108_, lean_object* v_nondep_1109_, lean_object* v_share1_1110_, lean_object* v_____r_1111_){
_start:
{
uint8_t v_nondep_boxed_1112_; lean_object* v_res_1113_; 
v_nondep_boxed_1112_ = lean_unbox(v_nondep_1109_);
v_res_1113_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__0(v_x_1105_, v_t_1106_, v_v_1107_, v_b_1108_, v_nondep_boxed_1112_, v_share1_1110_, v_____r_1111_);
return v_res_1113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__3(lean_object* v_assertShared_1114_, lean_object* v_v_1115_, lean_object* v_toBind_1116_, lean_object* v___f_1117_, lean_object* v_____r_1118_){
_start:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1119_ = lean_apply_1(v_assertShared_1114_, v_v_1115_);
v___x_1120_ = lean_apply_4(v_toBind_1116_, lean_box(0), lean_box(0), v___x_1119_, v___f_1117_);
return v___x_1120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1(lean_object* v___f_1121_, lean_object* v_assertShared_1122_, lean_object* v_b_1123_, lean_object* v_toBind_1124_, lean_object* v___f_1125_, lean_object* v_v_1126_, lean_object* v_t_1127_, uint8_t v_____do__lift_1128_){
_start:
{
if (v_____do__lift_1128_ == 0)
{
lean_object* v___x_1129_; lean_object* v___x_1130_; 
lean_dec_ref(v_t_1127_);
lean_dec_ref(v_v_1126_);
lean_dec(v___f_1125_);
lean_dec(v_toBind_1124_);
lean_dec_ref(v_b_1123_);
lean_dec(v_assertShared_1122_);
v___x_1129_ = lean_box(0);
v___x_1130_ = lean_apply_1(v___f_1121_, v___x_1129_);
return v___x_1130_;
}
else
{
lean_object* v___f_1131_; lean_object* v___f_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; 
lean_dec(v___f_1121_);
lean_inc(v_toBind_1124_);
lean_inc(v_assertShared_1122_);
v___f_1131_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__2), 5, 4);
lean_closure_set(v___f_1131_, 0, v_assertShared_1122_);
lean_closure_set(v___f_1131_, 1, v_b_1123_);
lean_closure_set(v___f_1131_, 2, v_toBind_1124_);
lean_closure_set(v___f_1131_, 3, v___f_1125_);
lean_inc(v_toBind_1124_);
lean_inc(v_assertShared_1122_);
v___f_1132_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__3), 5, 4);
lean_closure_set(v___f_1132_, 0, v_assertShared_1122_);
lean_closure_set(v___f_1132_, 1, v_v_1126_);
lean_closure_set(v___f_1132_, 2, v_toBind_1124_);
lean_closure_set(v___f_1132_, 3, v___f_1131_);
v___x_1133_ = lean_apply_1(v_assertShared_1122_, v_t_1127_);
v___x_1134_ = lean_apply_4(v_toBind_1124_, lean_box(0), lean_box(0), v___x_1133_, v___f_1132_);
return v___x_1134_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1___boxed(lean_object* v___f_1135_, lean_object* v_assertShared_1136_, lean_object* v_b_1137_, lean_object* v_toBind_1138_, lean_object* v___f_1139_, lean_object* v_v_1140_, lean_object* v_t_1141_, lean_object* v_____do__lift_1142_){
_start:
{
uint8_t v_____do__lift_122__boxed_1143_; lean_object* v_res_1144_; 
v_____do__lift_122__boxed_1143_ = lean_unbox(v_____do__lift_1142_);
v_res_1144_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1(v___f_1135_, v_assertShared_1136_, v_b_1137_, v_toBind_1138_, v___f_1139_, v_v_1140_, v_t_1141_, v_____do__lift_122__boxed_1143_);
return v_res_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg(lean_object* v_inst_1145_, lean_object* v_inst_1146_, lean_object* v_x_1147_, lean_object* v_t_1148_, lean_object* v_v_1149_, lean_object* v_b_1150_, uint8_t v_nondep_1151_){
_start:
{
lean_object* v_toBind_1152_; lean_object* v_share1_1153_; lean_object* v_assertShared_1154_; lean_object* v_isDebugEnabled_1155_; lean_object* v___x_1156_; lean_object* v___f_1157_; lean_object* v___f_1158_; lean_object* v___f_1159_; lean_object* v___x_1160_; 
v_toBind_1152_ = lean_ctor_get(v_inst_1146_, 1);
lean_inc(v_toBind_1152_);
lean_dec_ref(v_inst_1146_);
v_share1_1153_ = lean_ctor_get(v_inst_1145_, 0);
lean_inc(v_share1_1153_);
v_assertShared_1154_ = lean_ctor_get(v_inst_1145_, 1);
lean_inc(v_assertShared_1154_);
v_isDebugEnabled_1155_ = lean_ctor_get(v_inst_1145_, 2);
lean_inc(v_isDebugEnabled_1155_);
lean_dec_ref(v_inst_1145_);
v___x_1156_ = lean_box(v_nondep_1151_);
lean_inc_ref(v_b_1150_);
lean_inc_ref(v_v_1149_);
lean_inc_ref(v_t_1148_);
v___f_1157_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_1157_, 0, v_x_1147_);
lean_closure_set(v___f_1157_, 1, v_t_1148_);
lean_closure_set(v___f_1157_, 2, v_v_1149_);
lean_closure_set(v___f_1157_, 3, v_b_1150_);
lean_closure_set(v___f_1157_, 4, v___x_1156_);
lean_closure_set(v___f_1157_, 5, v_share1_1153_);
lean_inc_ref(v___f_1157_);
v___f_1158_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1158_, 0, v___f_1157_);
lean_inc(v_toBind_1152_);
v___f_1159_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_1159_, 0, v___f_1157_);
lean_closure_set(v___f_1159_, 1, v_assertShared_1154_);
lean_closure_set(v___f_1159_, 2, v_b_1150_);
lean_closure_set(v___f_1159_, 3, v_toBind_1152_);
lean_closure_set(v___f_1159_, 4, v___f_1158_);
lean_closure_set(v___f_1159_, 5, v_v_1149_);
lean_closure_set(v___f_1159_, 6, v_t_1148_);
v___x_1160_ = lean_apply_4(v_toBind_1152_, lean_box(0), lean_box(0), v_isDebugEnabled_1155_, v___f_1159_);
return v___x_1160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___boxed(lean_object* v_inst_1161_, lean_object* v_inst_1162_, lean_object* v_x_1163_, lean_object* v_t_1164_, lean_object* v_v_1165_, lean_object* v_b_1166_, lean_object* v_nondep_1167_){
_start:
{
uint8_t v_nondep_boxed_1168_; lean_object* v_res_1169_; 
v_nondep_boxed_1168_ = lean_unbox(v_nondep_1167_);
v_res_1169_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1161_, v_inst_1162_, v_x_1163_, v_t_1164_, v_v_1165_, v_b_1166_, v_nondep_boxed_1168_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS(lean_object* v_m_1170_, lean_object* v_inst_1171_, lean_object* v_inst_1172_, lean_object* v_x_1173_, lean_object* v_t_1174_, lean_object* v_v_1175_, lean_object* v_b_1176_, uint8_t v_nondep_1177_){
_start:
{
lean_object* v___x_1178_; 
v___x_1178_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1171_, v_inst_1172_, v_x_1173_, v_t_1174_, v_v_1175_, v_b_1176_, v_nondep_1177_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___boxed(lean_object* v_m_1179_, lean_object* v_inst_1180_, lean_object* v_inst_1181_, lean_object* v_x_1182_, lean_object* v_t_1183_, lean_object* v_v_1184_, lean_object* v_b_1185_, lean_object* v_nondep_1186_){
_start:
{
uint8_t v_nondep_boxed_1187_; lean_object* v_res_1188_; 
v_nondep_boxed_1187_ = lean_unbox(v_nondep_1186_);
v_res_1188_ = l_Lean_Meta_Sym_Internal_mkLetS(v_m_1179_, v_inst_1180_, v_inst_1181_, v_x_1182_, v_t_1183_, v_v_1184_, v_b_1185_, v_nondep_boxed_1187_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkHaveS___redArg___lam__0(lean_object* v_x_1189_, lean_object* v_t_1190_, lean_object* v_v_1191_, lean_object* v_b_1192_, lean_object* v_share1_1193_, lean_object* v_____r_1194_){
_start:
{
uint8_t v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1195_ = 1;
v___x_1196_ = l_Lean_Expr_letE___override(v_x_1189_, v_t_1190_, v_v_1191_, v_b_1192_, v___x_1195_);
v___x_1197_ = lean_apply_1(v_share1_1193_, v___x_1196_);
return v___x_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkHaveS___redArg(lean_object* v_inst_1198_, lean_object* v_inst_1199_, lean_object* v_x_1200_, lean_object* v_t_1201_, lean_object* v_v_1202_, lean_object* v_b_1203_){
_start:
{
lean_object* v_toBind_1204_; lean_object* v_share1_1205_; lean_object* v_assertShared_1206_; lean_object* v_isDebugEnabled_1207_; lean_object* v___f_1208_; lean_object* v___f_1209_; lean_object* v___f_1210_; lean_object* v___x_1211_; 
v_toBind_1204_ = lean_ctor_get(v_inst_1199_, 1);
lean_inc(v_toBind_1204_);
lean_dec_ref(v_inst_1199_);
v_share1_1205_ = lean_ctor_get(v_inst_1198_, 0);
lean_inc(v_share1_1205_);
v_assertShared_1206_ = lean_ctor_get(v_inst_1198_, 1);
lean_inc(v_assertShared_1206_);
v_isDebugEnabled_1207_ = lean_ctor_get(v_inst_1198_, 2);
lean_inc(v_isDebugEnabled_1207_);
lean_dec_ref(v_inst_1198_);
lean_inc_ref(v_b_1203_);
lean_inc_ref(v_v_1202_);
lean_inc_ref(v_t_1201_);
v___f_1208_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkHaveS___redArg___lam__0), 6, 5);
lean_closure_set(v___f_1208_, 0, v_x_1200_);
lean_closure_set(v___f_1208_, 1, v_t_1201_);
lean_closure_set(v___f_1208_, 2, v_v_1202_);
lean_closure_set(v___f_1208_, 3, v_b_1203_);
lean_closure_set(v___f_1208_, 4, v_share1_1205_);
lean_inc_ref(v___f_1208_);
v___f_1209_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1209_, 0, v___f_1208_);
lean_inc(v_toBind_1204_);
v___f_1210_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_1210_, 0, v___f_1208_);
lean_closure_set(v___f_1210_, 1, v_assertShared_1206_);
lean_closure_set(v___f_1210_, 2, v_b_1203_);
lean_closure_set(v___f_1210_, 3, v_toBind_1204_);
lean_closure_set(v___f_1210_, 4, v___f_1209_);
lean_closure_set(v___f_1210_, 5, v_v_1202_);
lean_closure_set(v___f_1210_, 6, v_t_1201_);
v___x_1211_ = lean_apply_4(v_toBind_1204_, lean_box(0), lean_box(0), v_isDebugEnabled_1207_, v___f_1210_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkHaveS(lean_object* v_m_1212_, lean_object* v_inst_1213_, lean_object* v_inst_1214_, lean_object* v_x_1215_, lean_object* v_t_1216_, lean_object* v_v_1217_, lean_object* v_b_1218_){
_start:
{
lean_object* v___x_1219_; 
v___x_1219_ = l_Lean_Meta_Sym_Internal_mkHaveS___redArg(v_inst_1213_, v_inst_1214_, v_x_1215_, v_t_1216_, v_v_1217_, v_b_1218_);
return v___x_1219_;
}
}
static lean_object* _init_l_Lean_Expr_updateAppS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1222_ = ((lean_object*)(l_Lean_Expr_updateAppS_x21___redArg___closed__1));
v___x_1223_ = lean_unsigned_to_nat(25u);
v___x_1224_ = lean_unsigned_to_nat(148u);
v___x_1225_ = ((lean_object*)(l_Lean_Expr_updateAppS_x21___redArg___closed__0));
v___x_1226_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1227_ = l_mkPanicMessageWithDecl(v___x_1226_, v___x_1225_, v___x_1224_, v___x_1223_, v___x_1222_);
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateAppS_x21___redArg(lean_object* v_inst_1228_, lean_object* v_inst_1229_, lean_object* v_e_1230_, lean_object* v_newFn_1231_, lean_object* v_newArg_1232_){
_start:
{
uint8_t v___y_1234_; 
if (lean_obj_tag(v_e_1230_) == 5)
{
lean_object* v_fn_1239_; lean_object* v_arg_1240_; uint8_t v___x_1241_; 
v_fn_1239_ = lean_ctor_get(v_e_1230_, 0);
v_arg_1240_ = lean_ctor_get(v_e_1230_, 1);
v___x_1241_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fn_1239_, v_newFn_1231_);
if (v___x_1241_ == 0)
{
v___y_1234_ = v___x_1241_;
goto v___jp_1233_;
}
else
{
uint8_t v___x_1242_; 
v___x_1242_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_1240_, v_newArg_1232_);
v___y_1234_ = v___x_1242_;
goto v___jp_1233_;
}
}
else
{
lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
lean_dec_ref(v_newArg_1232_);
lean_dec_ref(v_newFn_1231_);
lean_dec_ref(v_e_1230_);
lean_dec_ref(v_inst_1228_);
v___x_1243_ = l_Lean_instInhabitedExpr;
v___x_1244_ = l_instInhabitedOfMonad___redArg(v_inst_1229_, v___x_1243_);
v___x_1245_ = lean_obj_once(&l_Lean_Expr_updateAppS_x21___redArg___closed__2, &l_Lean_Expr_updateAppS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateAppS_x21___redArg___closed__2);
v___x_1246_ = l_panic___redArg(v___x_1244_, v___x_1245_);
return v___x_1246_;
}
v___jp_1233_:
{
if (v___y_1234_ == 0)
{
lean_object* v___x_1235_; 
lean_dec_ref(v_e_1230_);
v___x_1235_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1228_, v_inst_1229_, v_newFn_1231_, v_newArg_1232_);
return v___x_1235_;
}
else
{
lean_object* v_toApplicative_1236_; lean_object* v_toPure_1237_; lean_object* v___x_1238_; 
lean_dec_ref(v_newArg_1232_);
lean_dec_ref(v_newFn_1231_);
lean_dec_ref(v_inst_1228_);
v_toApplicative_1236_ = lean_ctor_get(v_inst_1229_, 0);
lean_inc_ref(v_toApplicative_1236_);
lean_dec_ref(v_inst_1229_);
v_toPure_1237_ = lean_ctor_get(v_toApplicative_1236_, 1);
lean_inc(v_toPure_1237_);
lean_dec_ref(v_toApplicative_1236_);
v___x_1238_ = lean_apply_2(v_toPure_1237_, lean_box(0), v_e_1230_);
return v___x_1238_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateAppS_x21(lean_object* v_m_1247_, lean_object* v_inst_1248_, lean_object* v_inst_1249_, lean_object* v_e_1250_, lean_object* v_newFn_1251_, lean_object* v_newArg_1252_){
_start:
{
uint8_t v___y_1254_; 
if (lean_obj_tag(v_e_1250_) == 5)
{
lean_object* v_fn_1259_; lean_object* v_arg_1260_; uint8_t v___x_1261_; 
v_fn_1259_ = lean_ctor_get(v_e_1250_, 0);
v_arg_1260_ = lean_ctor_get(v_e_1250_, 1);
v___x_1261_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fn_1259_, v_newFn_1251_);
if (v___x_1261_ == 0)
{
v___y_1254_ = v___x_1261_;
goto v___jp_1253_;
}
else
{
uint8_t v___x_1262_; 
v___x_1262_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_1260_, v_newArg_1252_);
v___y_1254_ = v___x_1262_;
goto v___jp_1253_;
}
}
else
{
lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; 
lean_dec_ref(v_newArg_1252_);
lean_dec_ref(v_newFn_1251_);
lean_dec_ref(v_e_1250_);
lean_dec_ref(v_inst_1248_);
v___x_1263_ = l_Lean_instInhabitedExpr;
v___x_1264_ = l_instInhabitedOfMonad___redArg(v_inst_1249_, v___x_1263_);
v___x_1265_ = lean_obj_once(&l_Lean_Expr_updateAppS_x21___redArg___closed__2, &l_Lean_Expr_updateAppS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateAppS_x21___redArg___closed__2);
v___x_1266_ = l_panic___redArg(v___x_1264_, v___x_1265_);
return v___x_1266_;
}
v___jp_1253_:
{
if (v___y_1254_ == 0)
{
lean_object* v___x_1255_; 
lean_dec_ref(v_e_1250_);
v___x_1255_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1248_, v_inst_1249_, v_newFn_1251_, v_newArg_1252_);
return v___x_1255_;
}
else
{
lean_object* v_toApplicative_1256_; lean_object* v_toPure_1257_; lean_object* v___x_1258_; 
lean_dec_ref(v_newArg_1252_);
lean_dec_ref(v_newFn_1251_);
lean_dec_ref(v_inst_1248_);
v_toApplicative_1256_ = lean_ctor_get(v_inst_1249_, 0);
lean_inc_ref(v_toApplicative_1256_);
lean_dec_ref(v_inst_1249_);
v_toPure_1257_ = lean_ctor_get(v_toApplicative_1256_, 1);
lean_inc(v_toPure_1257_);
lean_dec_ref(v_toApplicative_1256_);
v___x_1258_ = lean_apply_2(v_toPure_1257_, lean_box(0), v_e_1250_);
return v___x_1258_;
}
}
}
}
static lean_object* _init_l_Lean_Expr_updateMDataS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; 
v___x_1269_ = ((lean_object*)(l_Lean_Expr_updateMDataS_x21___redArg___closed__1));
v___x_1270_ = lean_unsigned_to_nat(24u);
v___x_1271_ = lean_unsigned_to_nat(152u);
v___x_1272_ = ((lean_object*)(l_Lean_Expr_updateMDataS_x21___redArg___closed__0));
v___x_1273_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1274_ = l_mkPanicMessageWithDecl(v___x_1273_, v___x_1272_, v___x_1271_, v___x_1270_, v___x_1269_);
return v___x_1274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateMDataS_x21___redArg(lean_object* v_inst_1275_, lean_object* v_inst_1276_, lean_object* v_e_1277_, lean_object* v_newExpr_1278_){
_start:
{
if (lean_obj_tag(v_e_1277_) == 10)
{
lean_object* v_data_1279_; lean_object* v_expr_1280_; uint8_t v___x_1281_; 
v_data_1279_ = lean_ctor_get(v_e_1277_, 0);
v_expr_1280_ = lean_ctor_get(v_e_1277_, 1);
v___x_1281_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_expr_1280_, v_newExpr_1278_);
if (v___x_1281_ == 0)
{
lean_object* v___x_1282_; 
lean_inc(v_data_1279_);
lean_dec_ref(v_e_1277_);
v___x_1282_ = l_Lean_Meta_Sym_Internal_mkMDataS___redArg(v_inst_1275_, v_inst_1276_, v_data_1279_, v_newExpr_1278_);
return v___x_1282_;
}
else
{
lean_object* v_toApplicative_1283_; lean_object* v_toPure_1284_; lean_object* v___x_1285_; 
lean_dec_ref(v_newExpr_1278_);
lean_dec_ref(v_inst_1275_);
v_toApplicative_1283_ = lean_ctor_get(v_inst_1276_, 0);
lean_inc_ref(v_toApplicative_1283_);
lean_dec_ref(v_inst_1276_);
v_toPure_1284_ = lean_ctor_get(v_toApplicative_1283_, 1);
lean_inc(v_toPure_1284_);
lean_dec_ref(v_toApplicative_1283_);
v___x_1285_ = lean_apply_2(v_toPure_1284_, lean_box(0), v_e_1277_);
return v___x_1285_;
}
}
else
{
lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; 
lean_dec_ref(v_newExpr_1278_);
lean_dec_ref(v_e_1277_);
lean_dec_ref(v_inst_1275_);
v___x_1286_ = l_Lean_instInhabitedExpr;
v___x_1287_ = l_instInhabitedOfMonad___redArg(v_inst_1276_, v___x_1286_);
v___x_1288_ = lean_obj_once(&l_Lean_Expr_updateMDataS_x21___redArg___closed__2, &l_Lean_Expr_updateMDataS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateMDataS_x21___redArg___closed__2);
v___x_1289_ = l_panic___redArg(v___x_1287_, v___x_1288_);
return v___x_1289_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateMDataS_x21(lean_object* v_m_1290_, lean_object* v_inst_1291_, lean_object* v_inst_1292_, lean_object* v_e_1293_, lean_object* v_newExpr_1294_){
_start:
{
if (lean_obj_tag(v_e_1293_) == 10)
{
lean_object* v_data_1295_; lean_object* v_expr_1296_; uint8_t v___x_1297_; 
v_data_1295_ = lean_ctor_get(v_e_1293_, 0);
v_expr_1296_ = lean_ctor_get(v_e_1293_, 1);
v___x_1297_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_expr_1296_, v_newExpr_1294_);
if (v___x_1297_ == 0)
{
lean_object* v___x_1298_; 
lean_inc(v_data_1295_);
lean_dec_ref(v_e_1293_);
v___x_1298_ = l_Lean_Meta_Sym_Internal_mkMDataS___redArg(v_inst_1291_, v_inst_1292_, v_data_1295_, v_newExpr_1294_);
return v___x_1298_;
}
else
{
lean_object* v_toApplicative_1299_; lean_object* v_toPure_1300_; lean_object* v___x_1301_; 
lean_dec_ref(v_newExpr_1294_);
lean_dec_ref(v_inst_1291_);
v_toApplicative_1299_ = lean_ctor_get(v_inst_1292_, 0);
lean_inc_ref(v_toApplicative_1299_);
lean_dec_ref(v_inst_1292_);
v_toPure_1300_ = lean_ctor_get(v_toApplicative_1299_, 1);
lean_inc(v_toPure_1300_);
lean_dec_ref(v_toApplicative_1299_);
v___x_1301_ = lean_apply_2(v_toPure_1300_, lean_box(0), v_e_1293_);
return v___x_1301_;
}
}
else
{
lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; 
lean_dec_ref(v_newExpr_1294_);
lean_dec_ref(v_e_1293_);
lean_dec_ref(v_inst_1291_);
v___x_1302_ = l_Lean_instInhabitedExpr;
v___x_1303_ = l_instInhabitedOfMonad___redArg(v_inst_1292_, v___x_1302_);
v___x_1304_ = lean_obj_once(&l_Lean_Expr_updateMDataS_x21___redArg___closed__2, &l_Lean_Expr_updateMDataS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateMDataS_x21___redArg___closed__2);
v___x_1305_ = l_panic___redArg(v___x_1303_, v___x_1304_);
return v___x_1305_;
}
}
}
static lean_object* _init_l_Lean_Expr_updateProjS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1308_ = ((lean_object*)(l_Lean_Expr_updateProjS_x21___redArg___closed__1));
v___x_1309_ = lean_unsigned_to_nat(25u);
v___x_1310_ = lean_unsigned_to_nat(156u);
v___x_1311_ = ((lean_object*)(l_Lean_Expr_updateProjS_x21___redArg___closed__0));
v___x_1312_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1313_ = l_mkPanicMessageWithDecl(v___x_1312_, v___x_1311_, v___x_1310_, v___x_1309_, v___x_1308_);
return v___x_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateProjS_x21___redArg(lean_object* v_inst_1314_, lean_object* v_inst_1315_, lean_object* v_e_1316_, lean_object* v_newExpr_1317_){
_start:
{
if (lean_obj_tag(v_e_1316_) == 11)
{
lean_object* v_typeName_1318_; lean_object* v_idx_1319_; lean_object* v_struct_1320_; uint8_t v___x_1321_; 
v_typeName_1318_ = lean_ctor_get(v_e_1316_, 0);
v_idx_1319_ = lean_ctor_get(v_e_1316_, 1);
v_struct_1320_ = lean_ctor_get(v_e_1316_, 2);
v___x_1321_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_1320_, v_newExpr_1317_);
if (v___x_1321_ == 0)
{
lean_object* v___x_1322_; 
lean_inc(v_idx_1319_);
lean_inc(v_typeName_1318_);
lean_dec_ref(v_e_1316_);
v___x_1322_ = l_Lean_Meta_Sym_Internal_mkProjS___redArg(v_inst_1314_, v_inst_1315_, v_typeName_1318_, v_idx_1319_, v_newExpr_1317_);
return v___x_1322_;
}
else
{
lean_object* v_toApplicative_1323_; lean_object* v_toPure_1324_; lean_object* v___x_1325_; 
lean_dec_ref(v_newExpr_1317_);
lean_dec_ref(v_inst_1314_);
v_toApplicative_1323_ = lean_ctor_get(v_inst_1315_, 0);
lean_inc_ref(v_toApplicative_1323_);
lean_dec_ref(v_inst_1315_);
v_toPure_1324_ = lean_ctor_get(v_toApplicative_1323_, 1);
lean_inc(v_toPure_1324_);
lean_dec_ref(v_toApplicative_1323_);
v___x_1325_ = lean_apply_2(v_toPure_1324_, lean_box(0), v_e_1316_);
return v___x_1325_;
}
}
else
{
lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; 
lean_dec_ref(v_newExpr_1317_);
lean_dec_ref(v_e_1316_);
lean_dec_ref(v_inst_1314_);
v___x_1326_ = l_Lean_instInhabitedExpr;
v___x_1327_ = l_instInhabitedOfMonad___redArg(v_inst_1315_, v___x_1326_);
v___x_1328_ = lean_obj_once(&l_Lean_Expr_updateProjS_x21___redArg___closed__2, &l_Lean_Expr_updateProjS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateProjS_x21___redArg___closed__2);
v___x_1329_ = l_panic___redArg(v___x_1327_, v___x_1328_);
return v___x_1329_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateProjS_x21(lean_object* v_m_1330_, lean_object* v_inst_1331_, lean_object* v_inst_1332_, lean_object* v_e_1333_, lean_object* v_newExpr_1334_){
_start:
{
if (lean_obj_tag(v_e_1333_) == 11)
{
lean_object* v_typeName_1335_; lean_object* v_idx_1336_; lean_object* v_struct_1337_; uint8_t v___x_1338_; 
v_typeName_1335_ = lean_ctor_get(v_e_1333_, 0);
v_idx_1336_ = lean_ctor_get(v_e_1333_, 1);
v_struct_1337_ = lean_ctor_get(v_e_1333_, 2);
v___x_1338_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_1337_, v_newExpr_1334_);
if (v___x_1338_ == 0)
{
lean_object* v___x_1339_; 
lean_inc(v_idx_1336_);
lean_inc(v_typeName_1335_);
lean_dec_ref(v_e_1333_);
v___x_1339_ = l_Lean_Meta_Sym_Internal_mkProjS___redArg(v_inst_1331_, v_inst_1332_, v_typeName_1335_, v_idx_1336_, v_newExpr_1334_);
return v___x_1339_;
}
else
{
lean_object* v_toApplicative_1340_; lean_object* v_toPure_1341_; lean_object* v___x_1342_; 
lean_dec_ref(v_newExpr_1334_);
lean_dec_ref(v_inst_1331_);
v_toApplicative_1340_ = lean_ctor_get(v_inst_1332_, 0);
lean_inc_ref(v_toApplicative_1340_);
lean_dec_ref(v_inst_1332_);
v_toPure_1341_ = lean_ctor_get(v_toApplicative_1340_, 1);
lean_inc(v_toPure_1341_);
lean_dec_ref(v_toApplicative_1340_);
v___x_1342_ = lean_apply_2(v_toPure_1341_, lean_box(0), v_e_1333_);
return v___x_1342_;
}
}
else
{
lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; 
lean_dec_ref(v_newExpr_1334_);
lean_dec_ref(v_e_1333_);
lean_dec_ref(v_inst_1331_);
v___x_1343_ = l_Lean_instInhabitedExpr;
v___x_1344_ = l_instInhabitedOfMonad___redArg(v_inst_1332_, v___x_1343_);
v___x_1345_ = lean_obj_once(&l_Lean_Expr_updateProjS_x21___redArg___closed__2, &l_Lean_Expr_updateProjS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateProjS_x21___redArg___closed__2);
v___x_1346_ = l_panic___redArg(v___x_1344_, v___x_1345_);
return v___x_1346_;
}
}
}
static lean_object* _init_l_Lean_Expr_updateForallS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; 
v___x_1349_ = ((lean_object*)(l_Lean_Expr_updateForallS_x21___redArg___closed__1));
v___x_1350_ = lean_unsigned_to_nat(31u);
v___x_1351_ = lean_unsigned_to_nat(160u);
v___x_1352_ = ((lean_object*)(l_Lean_Expr_updateForallS_x21___redArg___closed__0));
v___x_1353_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1354_ = l_mkPanicMessageWithDecl(v___x_1353_, v___x_1352_, v___x_1351_, v___x_1350_, v___x_1349_);
return v___x_1354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallS_x21___redArg(lean_object* v_inst_1355_, lean_object* v_inst_1356_, lean_object* v_e_1357_, lean_object* v_newDomain_1358_, lean_object* v_newBody_1359_){
_start:
{
if (lean_obj_tag(v_e_1357_) == 7)
{
lean_object* v_binderName_1360_; lean_object* v_binderType_1361_; lean_object* v_body_1362_; uint8_t v_binderInfo_1363_; uint8_t v___y_1365_; uint8_t v___x_1370_; 
v_binderName_1360_ = lean_ctor_get(v_e_1357_, 0);
v_binderType_1361_ = lean_ctor_get(v_e_1357_, 1);
v_body_1362_ = lean_ctor_get(v_e_1357_, 2);
v_binderInfo_1363_ = lean_ctor_get_uint8(v_e_1357_, sizeof(void*)*3 + 8);
v___x_1370_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_1361_, v_newDomain_1358_);
if (v___x_1370_ == 0)
{
v___y_1365_ = v___x_1370_;
goto v___jp_1364_;
}
else
{
uint8_t v___x_1371_; 
v___x_1371_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1362_, v_newBody_1359_);
v___y_1365_ = v___x_1371_;
goto v___jp_1364_;
}
v___jp_1364_:
{
if (v___y_1365_ == 0)
{
lean_object* v___x_1366_; 
lean_inc(v_binderName_1360_);
lean_dec_ref(v_e_1357_);
v___x_1366_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v_inst_1355_, v_inst_1356_, v_binderName_1360_, v_binderInfo_1363_, v_newDomain_1358_, v_newBody_1359_);
return v___x_1366_;
}
else
{
lean_object* v_toApplicative_1367_; lean_object* v_toPure_1368_; lean_object* v___x_1369_; 
lean_dec_ref(v_newBody_1359_);
lean_dec_ref(v_newDomain_1358_);
lean_dec_ref(v_inst_1355_);
v_toApplicative_1367_ = lean_ctor_get(v_inst_1356_, 0);
lean_inc_ref(v_toApplicative_1367_);
lean_dec_ref(v_inst_1356_);
v_toPure_1368_ = lean_ctor_get(v_toApplicative_1367_, 1);
lean_inc(v_toPure_1368_);
lean_dec_ref(v_toApplicative_1367_);
v___x_1369_ = lean_apply_2(v_toPure_1368_, lean_box(0), v_e_1357_);
return v___x_1369_;
}
}
}
else
{
lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; 
lean_dec_ref(v_newBody_1359_);
lean_dec_ref(v_newDomain_1358_);
lean_dec_ref(v_e_1357_);
lean_dec_ref(v_inst_1355_);
v___x_1372_ = l_Lean_instInhabitedExpr;
v___x_1373_ = l_instInhabitedOfMonad___redArg(v_inst_1356_, v___x_1372_);
v___x_1374_ = lean_obj_once(&l_Lean_Expr_updateForallS_x21___redArg___closed__2, &l_Lean_Expr_updateForallS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateForallS_x21___redArg___closed__2);
v___x_1375_ = l_panic___redArg(v___x_1373_, v___x_1374_);
return v___x_1375_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallS_x21(lean_object* v_m_1376_, lean_object* v_inst_1377_, lean_object* v_inst_1378_, lean_object* v_e_1379_, lean_object* v_newDomain_1380_, lean_object* v_newBody_1381_){
_start:
{
if (lean_obj_tag(v_e_1379_) == 7)
{
lean_object* v_binderName_1382_; lean_object* v_binderType_1383_; lean_object* v_body_1384_; uint8_t v_binderInfo_1385_; uint8_t v___y_1387_; uint8_t v___x_1392_; 
v_binderName_1382_ = lean_ctor_get(v_e_1379_, 0);
v_binderType_1383_ = lean_ctor_get(v_e_1379_, 1);
v_body_1384_ = lean_ctor_get(v_e_1379_, 2);
v_binderInfo_1385_ = lean_ctor_get_uint8(v_e_1379_, sizeof(void*)*3 + 8);
v___x_1392_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_1383_, v_newDomain_1380_);
if (v___x_1392_ == 0)
{
v___y_1387_ = v___x_1392_;
goto v___jp_1386_;
}
else
{
uint8_t v___x_1393_; 
v___x_1393_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1384_, v_newBody_1381_);
v___y_1387_ = v___x_1393_;
goto v___jp_1386_;
}
v___jp_1386_:
{
if (v___y_1387_ == 0)
{
lean_object* v___x_1388_; 
lean_inc(v_binderName_1382_);
lean_dec_ref(v_e_1379_);
v___x_1388_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v_inst_1377_, v_inst_1378_, v_binderName_1382_, v_binderInfo_1385_, v_newDomain_1380_, v_newBody_1381_);
return v___x_1388_;
}
else
{
lean_object* v_toApplicative_1389_; lean_object* v_toPure_1390_; lean_object* v___x_1391_; 
lean_dec_ref(v_newBody_1381_);
lean_dec_ref(v_newDomain_1380_);
lean_dec_ref(v_inst_1377_);
v_toApplicative_1389_ = lean_ctor_get(v_inst_1378_, 0);
lean_inc_ref(v_toApplicative_1389_);
lean_dec_ref(v_inst_1378_);
v_toPure_1390_ = lean_ctor_get(v_toApplicative_1389_, 1);
lean_inc(v_toPure_1390_);
lean_dec_ref(v_toApplicative_1389_);
v___x_1391_ = lean_apply_2(v_toPure_1390_, lean_box(0), v_e_1379_);
return v___x_1391_;
}
}
}
else
{
lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; 
lean_dec_ref(v_newBody_1381_);
lean_dec_ref(v_newDomain_1380_);
lean_dec_ref(v_e_1379_);
lean_dec_ref(v_inst_1377_);
v___x_1394_ = l_Lean_instInhabitedExpr;
v___x_1395_ = l_instInhabitedOfMonad___redArg(v_inst_1378_, v___x_1394_);
v___x_1396_ = lean_obj_once(&l_Lean_Expr_updateForallS_x21___redArg___closed__2, &l_Lean_Expr_updateForallS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateForallS_x21___redArg___closed__2);
v___x_1397_ = l_panic___redArg(v___x_1395_, v___x_1396_);
return v___x_1397_;
}
}
}
static lean_object* _init_l_Lean_Expr_updateLambdaS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
v___x_1400_ = ((lean_object*)(l_Lean_Expr_updateLambdaS_x21___redArg___closed__1));
v___x_1401_ = lean_unsigned_to_nat(27u);
v___x_1402_ = lean_unsigned_to_nat(167u);
v___x_1403_ = ((lean_object*)(l_Lean_Expr_updateLambdaS_x21___redArg___closed__0));
v___x_1404_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1405_ = l_mkPanicMessageWithDecl(v___x_1404_, v___x_1403_, v___x_1402_, v___x_1401_, v___x_1400_);
return v___x_1405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLambdaS_x21___redArg(lean_object* v_inst_1406_, lean_object* v_inst_1407_, lean_object* v_e_1408_, lean_object* v_newDomain_1409_, lean_object* v_newBody_1410_){
_start:
{
if (lean_obj_tag(v_e_1408_) == 6)
{
lean_object* v_binderName_1411_; lean_object* v_binderType_1412_; lean_object* v_body_1413_; uint8_t v_binderInfo_1414_; uint8_t v___y_1416_; uint8_t v___x_1421_; 
v_binderName_1411_ = lean_ctor_get(v_e_1408_, 0);
v_binderType_1412_ = lean_ctor_get(v_e_1408_, 1);
v_body_1413_ = lean_ctor_get(v_e_1408_, 2);
v_binderInfo_1414_ = lean_ctor_get_uint8(v_e_1408_, sizeof(void*)*3 + 8);
v___x_1421_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_1412_, v_newDomain_1409_);
if (v___x_1421_ == 0)
{
v___y_1416_ = v___x_1421_;
goto v___jp_1415_;
}
else
{
uint8_t v___x_1422_; 
v___x_1422_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1413_, v_newBody_1410_);
v___y_1416_ = v___x_1422_;
goto v___jp_1415_;
}
v___jp_1415_:
{
if (v___y_1416_ == 0)
{
lean_object* v___x_1417_; 
lean_inc(v_binderName_1411_);
lean_dec_ref(v_e_1408_);
v___x_1417_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v_inst_1406_, v_inst_1407_, v_binderName_1411_, v_binderInfo_1414_, v_newDomain_1409_, v_newBody_1410_);
return v___x_1417_;
}
else
{
lean_object* v_toApplicative_1418_; lean_object* v_toPure_1419_; lean_object* v___x_1420_; 
lean_dec_ref(v_newBody_1410_);
lean_dec_ref(v_newDomain_1409_);
lean_dec_ref(v_inst_1406_);
v_toApplicative_1418_ = lean_ctor_get(v_inst_1407_, 0);
lean_inc_ref(v_toApplicative_1418_);
lean_dec_ref(v_inst_1407_);
v_toPure_1419_ = lean_ctor_get(v_toApplicative_1418_, 1);
lean_inc(v_toPure_1419_);
lean_dec_ref(v_toApplicative_1418_);
v___x_1420_ = lean_apply_2(v_toPure_1419_, lean_box(0), v_e_1408_);
return v___x_1420_;
}
}
}
else
{
lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; 
lean_dec_ref(v_newBody_1410_);
lean_dec_ref(v_newDomain_1409_);
lean_dec_ref(v_e_1408_);
lean_dec_ref(v_inst_1406_);
v___x_1423_ = l_Lean_instInhabitedExpr;
v___x_1424_ = l_instInhabitedOfMonad___redArg(v_inst_1407_, v___x_1423_);
v___x_1425_ = lean_obj_once(&l_Lean_Expr_updateLambdaS_x21___redArg___closed__2, &l_Lean_Expr_updateLambdaS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateLambdaS_x21___redArg___closed__2);
v___x_1426_ = l_panic___redArg(v___x_1424_, v___x_1425_);
return v___x_1426_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLambdaS_x21(lean_object* v_m_1427_, lean_object* v_inst_1428_, lean_object* v_inst_1429_, lean_object* v_e_1430_, lean_object* v_newDomain_1431_, lean_object* v_newBody_1432_){
_start:
{
if (lean_obj_tag(v_e_1430_) == 6)
{
lean_object* v_binderName_1433_; lean_object* v_binderType_1434_; lean_object* v_body_1435_; uint8_t v_binderInfo_1436_; uint8_t v___y_1438_; uint8_t v___x_1443_; 
v_binderName_1433_ = lean_ctor_get(v_e_1430_, 0);
v_binderType_1434_ = lean_ctor_get(v_e_1430_, 1);
v_body_1435_ = lean_ctor_get(v_e_1430_, 2);
v_binderInfo_1436_ = lean_ctor_get_uint8(v_e_1430_, sizeof(void*)*3 + 8);
v___x_1443_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_1434_, v_newDomain_1431_);
if (v___x_1443_ == 0)
{
v___y_1438_ = v___x_1443_;
goto v___jp_1437_;
}
else
{
uint8_t v___x_1444_; 
v___x_1444_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1435_, v_newBody_1432_);
v___y_1438_ = v___x_1444_;
goto v___jp_1437_;
}
v___jp_1437_:
{
if (v___y_1438_ == 0)
{
lean_object* v___x_1439_; 
lean_inc(v_binderName_1433_);
lean_dec_ref(v_e_1430_);
v___x_1439_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v_inst_1428_, v_inst_1429_, v_binderName_1433_, v_binderInfo_1436_, v_newDomain_1431_, v_newBody_1432_);
return v___x_1439_;
}
else
{
lean_object* v_toApplicative_1440_; lean_object* v_toPure_1441_; lean_object* v___x_1442_; 
lean_dec_ref(v_newBody_1432_);
lean_dec_ref(v_newDomain_1431_);
lean_dec_ref(v_inst_1428_);
v_toApplicative_1440_ = lean_ctor_get(v_inst_1429_, 0);
lean_inc_ref(v_toApplicative_1440_);
lean_dec_ref(v_inst_1429_);
v_toPure_1441_ = lean_ctor_get(v_toApplicative_1440_, 1);
lean_inc(v_toPure_1441_);
lean_dec_ref(v_toApplicative_1440_);
v___x_1442_ = lean_apply_2(v_toPure_1441_, lean_box(0), v_e_1430_);
return v___x_1442_;
}
}
}
else
{
lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; 
lean_dec_ref(v_newBody_1432_);
lean_dec_ref(v_newDomain_1431_);
lean_dec_ref(v_e_1430_);
lean_dec_ref(v_inst_1428_);
v___x_1445_ = l_Lean_instInhabitedExpr;
v___x_1446_ = l_instInhabitedOfMonad___redArg(v_inst_1429_, v___x_1445_);
v___x_1447_ = lean_obj_once(&l_Lean_Expr_updateLambdaS_x21___redArg___closed__2, &l_Lean_Expr_updateLambdaS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateLambdaS_x21___redArg___closed__2);
v___x_1448_ = l_panic___redArg(v___x_1446_, v___x_1447_);
return v___x_1448_;
}
}
}
static lean_object* _init_l_Lean_Expr_updateLetS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; 
v___x_1451_ = ((lean_object*)(l_Lean_Expr_updateLetS_x21___redArg___closed__1));
v___x_1452_ = lean_unsigned_to_nat(34u);
v___x_1453_ = lean_unsigned_to_nat(174u);
v___x_1454_ = ((lean_object*)(l_Lean_Expr_updateLetS_x21___redArg___closed__0));
v___x_1455_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1456_ = l_mkPanicMessageWithDecl(v___x_1455_, v___x_1454_, v___x_1453_, v___x_1452_, v___x_1451_);
return v___x_1456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLetS_x21___redArg(lean_object* v_inst_1457_, lean_object* v_inst_1458_, lean_object* v_e_1459_, lean_object* v_newType_1460_, lean_object* v_newVal_1461_, lean_object* v_newBody_1462_){
_start:
{
if (lean_obj_tag(v_e_1459_) == 8)
{
lean_object* v_declName_1463_; lean_object* v_type_1464_; lean_object* v_value_1465_; lean_object* v_body_1466_; uint8_t v_nondep_1467_; uint8_t v___y_1469_; uint8_t v___x_1476_; 
v_declName_1463_ = lean_ctor_get(v_e_1459_, 0);
v_type_1464_ = lean_ctor_get(v_e_1459_, 1);
v_value_1465_ = lean_ctor_get(v_e_1459_, 2);
v_body_1466_ = lean_ctor_get(v_e_1459_, 3);
v_nondep_1467_ = lean_ctor_get_uint8(v_e_1459_, sizeof(void*)*4 + 8);
v___x_1476_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_type_1464_, v_newType_1460_);
if (v___x_1476_ == 0)
{
v___y_1469_ = v___x_1476_;
goto v___jp_1468_;
}
else
{
uint8_t v___x_1477_; 
v___x_1477_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_value_1465_, v_newVal_1461_);
v___y_1469_ = v___x_1477_;
goto v___jp_1468_;
}
v___jp_1468_:
{
if (v___y_1469_ == 0)
{
lean_object* v___x_1470_; 
lean_inc(v_declName_1463_);
lean_dec_ref(v_e_1459_);
v___x_1470_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1457_, v_inst_1458_, v_declName_1463_, v_newType_1460_, v_newVal_1461_, v_newBody_1462_, v_nondep_1467_);
return v___x_1470_;
}
else
{
uint8_t v___x_1471_; 
v___x_1471_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1466_, v_newBody_1462_);
if (v___x_1471_ == 0)
{
lean_object* v___x_1472_; 
lean_inc(v_declName_1463_);
lean_dec_ref(v_e_1459_);
v___x_1472_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1457_, v_inst_1458_, v_declName_1463_, v_newType_1460_, v_newVal_1461_, v_newBody_1462_, v_nondep_1467_);
return v___x_1472_;
}
else
{
lean_object* v_toApplicative_1473_; lean_object* v_toPure_1474_; lean_object* v___x_1475_; 
lean_dec_ref(v_newBody_1462_);
lean_dec_ref(v_newVal_1461_);
lean_dec_ref(v_newType_1460_);
lean_dec_ref(v_inst_1457_);
v_toApplicative_1473_ = lean_ctor_get(v_inst_1458_, 0);
lean_inc_ref(v_toApplicative_1473_);
lean_dec_ref(v_inst_1458_);
v_toPure_1474_ = lean_ctor_get(v_toApplicative_1473_, 1);
lean_inc(v_toPure_1474_);
lean_dec_ref(v_toApplicative_1473_);
v___x_1475_ = lean_apply_2(v_toPure_1474_, lean_box(0), v_e_1459_);
return v___x_1475_;
}
}
}
}
else
{
lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; 
lean_dec_ref(v_newBody_1462_);
lean_dec_ref(v_newVal_1461_);
lean_dec_ref(v_newType_1460_);
lean_dec_ref(v_e_1459_);
lean_dec_ref(v_inst_1457_);
v___x_1478_ = l_Lean_instInhabitedExpr;
v___x_1479_ = l_instInhabitedOfMonad___redArg(v_inst_1458_, v___x_1478_);
v___x_1480_ = lean_obj_once(&l_Lean_Expr_updateLetS_x21___redArg___closed__2, &l_Lean_Expr_updateLetS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateLetS_x21___redArg___closed__2);
v___x_1481_ = l_panic___redArg(v___x_1479_, v___x_1480_);
return v___x_1481_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLetS_x21(lean_object* v_m_1482_, lean_object* v_inst_1483_, lean_object* v_inst_1484_, lean_object* v_e_1485_, lean_object* v_newType_1486_, lean_object* v_newVal_1487_, lean_object* v_newBody_1488_){
_start:
{
if (lean_obj_tag(v_e_1485_) == 8)
{
lean_object* v_declName_1489_; lean_object* v_type_1490_; lean_object* v_value_1491_; lean_object* v_body_1492_; uint8_t v_nondep_1493_; uint8_t v___y_1495_; uint8_t v___x_1502_; 
v_declName_1489_ = lean_ctor_get(v_e_1485_, 0);
v_type_1490_ = lean_ctor_get(v_e_1485_, 1);
v_value_1491_ = lean_ctor_get(v_e_1485_, 2);
v_body_1492_ = lean_ctor_get(v_e_1485_, 3);
v_nondep_1493_ = lean_ctor_get_uint8(v_e_1485_, sizeof(void*)*4 + 8);
v___x_1502_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_type_1490_, v_newType_1486_);
if (v___x_1502_ == 0)
{
v___y_1495_ = v___x_1502_;
goto v___jp_1494_;
}
else
{
uint8_t v___x_1503_; 
v___x_1503_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_value_1491_, v_newVal_1487_);
v___y_1495_ = v___x_1503_;
goto v___jp_1494_;
}
v___jp_1494_:
{
if (v___y_1495_ == 0)
{
lean_object* v___x_1496_; 
lean_inc(v_declName_1489_);
lean_dec_ref(v_e_1485_);
v___x_1496_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1483_, v_inst_1484_, v_declName_1489_, v_newType_1486_, v_newVal_1487_, v_newBody_1488_, v_nondep_1493_);
return v___x_1496_;
}
else
{
uint8_t v___x_1497_; 
v___x_1497_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1492_, v_newBody_1488_);
if (v___x_1497_ == 0)
{
lean_object* v___x_1498_; 
lean_inc(v_declName_1489_);
lean_dec_ref(v_e_1485_);
v___x_1498_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1483_, v_inst_1484_, v_declName_1489_, v_newType_1486_, v_newVal_1487_, v_newBody_1488_, v_nondep_1493_);
return v___x_1498_;
}
else
{
lean_object* v_toApplicative_1499_; lean_object* v_toPure_1500_; lean_object* v___x_1501_; 
lean_dec_ref(v_newBody_1488_);
lean_dec_ref(v_newVal_1487_);
lean_dec_ref(v_newType_1486_);
lean_dec_ref(v_inst_1483_);
v_toApplicative_1499_ = lean_ctor_get(v_inst_1484_, 0);
lean_inc_ref(v_toApplicative_1499_);
lean_dec_ref(v_inst_1484_);
v_toPure_1500_ = lean_ctor_get(v_toApplicative_1499_, 1);
lean_inc(v_toPure_1500_);
lean_dec_ref(v_toApplicative_1499_);
v___x_1501_ = lean_apply_2(v_toPure_1500_, lean_box(0), v_e_1485_);
return v___x_1501_;
}
}
}
}
else
{
lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; 
lean_dec_ref(v_newBody_1488_);
lean_dec_ref(v_newVal_1487_);
lean_dec_ref(v_newType_1486_);
lean_dec_ref(v_e_1485_);
lean_dec_ref(v_inst_1483_);
v___x_1504_ = l_Lean_instInhabitedExpr;
v___x_1505_ = l_instInhabitedOfMonad___redArg(v_inst_1484_, v___x_1504_);
v___x_1506_ = lean_obj_once(&l_Lean_Expr_updateLetS_x21___redArg___closed__2, &l_Lean_Expr_updateLetS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateLetS_x21___redArg___closed__2);
v___x_1507_ = l_panic___redArg(v___x_1505_, v___x_1506_);
return v___x_1507_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___redArg___lam__0(lean_object* v_inst_1508_, lean_object* v_inst_1509_, lean_object* v_a_u2082_1510_, lean_object* v_____do__lift_1511_){
_start:
{
lean_object* v___x_1512_; 
v___x_1512_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1508_, v_inst_1509_, v_____do__lift_1511_, v_a_u2082_1510_);
return v___x_1512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___redArg(lean_object* v_inst_1513_, lean_object* v_inst_1514_, lean_object* v_f_1515_, lean_object* v_a_u2081_1516_, lean_object* v_a_u2082_1517_){
_start:
{
lean_object* v_toBind_1518_; lean_object* v___f_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; 
v_toBind_1518_ = lean_ctor_get(v_inst_1514_, 1);
lean_inc(v_toBind_1518_);
lean_inc_ref(v_inst_1514_);
lean_inc_ref(v_inst_1513_);
v___f_1519_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2082___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1519_, 0, v_inst_1513_);
lean_closure_set(v___f_1519_, 1, v_inst_1514_);
lean_closure_set(v___f_1519_, 2, v_a_u2082_1517_);
v___x_1520_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1513_, v_inst_1514_, v_f_1515_, v_a_u2081_1516_);
v___x_1521_ = lean_apply_4(v_toBind_1518_, lean_box(0), lean_box(0), v___x_1520_, v___f_1519_);
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082(lean_object* v_m_1522_, lean_object* v_inst_1523_, lean_object* v_inst_1524_, lean_object* v_f_1525_, lean_object* v_a_u2081_1526_, lean_object* v_a_u2082_1527_){
_start:
{
lean_object* v___x_1528_; 
v___x_1528_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___redArg(v_inst_1523_, v_inst_1524_, v_f_1525_, v_a_u2081_1526_, v_a_u2082_1527_);
return v___x_1528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___redArg___lam__0(lean_object* v_inst_1529_, lean_object* v_inst_1530_, lean_object* v_a_u2083_1531_, lean_object* v_____do__lift_1532_){
_start:
{
lean_object* v___x_1533_; 
v___x_1533_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1529_, v_inst_1530_, v_____do__lift_1532_, v_a_u2083_1531_);
return v___x_1533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___redArg(lean_object* v_inst_1534_, lean_object* v_inst_1535_, lean_object* v_f_1536_, lean_object* v_a_u2081_1537_, lean_object* v_a_u2082_1538_, lean_object* v_a_u2083_1539_){
_start:
{
lean_object* v_toBind_1540_; lean_object* v___f_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; 
v_toBind_1540_ = lean_ctor_get(v_inst_1535_, 1);
lean_inc(v_toBind_1540_);
lean_inc_ref(v_inst_1535_);
lean_inc_ref(v_inst_1534_);
v___f_1541_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2083___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1541_, 0, v_inst_1534_);
lean_closure_set(v___f_1541_, 1, v_inst_1535_);
lean_closure_set(v___f_1541_, 2, v_a_u2083_1539_);
v___x_1542_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___redArg(v_inst_1534_, v_inst_1535_, v_f_1536_, v_a_u2081_1537_, v_a_u2082_1538_);
v___x_1543_ = lean_apply_4(v_toBind_1540_, lean_box(0), lean_box(0), v___x_1542_, v___f_1541_);
return v___x_1543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083(lean_object* v_m_1544_, lean_object* v_inst_1545_, lean_object* v_inst_1546_, lean_object* v_f_1547_, lean_object* v_a_u2081_1548_, lean_object* v_a_u2082_1549_, lean_object* v_a_u2083_1550_){
_start:
{
lean_object* v___x_1551_; 
v___x_1551_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___redArg(v_inst_1545_, v_inst_1546_, v_f_1547_, v_a_u2081_1548_, v_a_u2082_1549_, v_a_u2083_1550_);
return v___x_1551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___redArg___lam__0(lean_object* v_inst_1552_, lean_object* v_inst_1553_, lean_object* v_a_u2084_1554_, lean_object* v_____do__lift_1555_){
_start:
{
lean_object* v___x_1556_; 
v___x_1556_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1552_, v_inst_1553_, v_____do__lift_1555_, v_a_u2084_1554_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___redArg(lean_object* v_inst_1557_, lean_object* v_inst_1558_, lean_object* v_f_1559_, lean_object* v_a_u2081_1560_, lean_object* v_a_u2082_1561_, lean_object* v_a_u2083_1562_, lean_object* v_a_u2084_1563_){
_start:
{
lean_object* v_toBind_1564_; lean_object* v___f_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; 
v_toBind_1564_ = lean_ctor_get(v_inst_1558_, 1);
lean_inc(v_toBind_1564_);
lean_inc_ref(v_inst_1558_);
lean_inc_ref(v_inst_1557_);
v___f_1565_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2084___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1565_, 0, v_inst_1557_);
lean_closure_set(v___f_1565_, 1, v_inst_1558_);
lean_closure_set(v___f_1565_, 2, v_a_u2084_1563_);
v___x_1566_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___redArg(v_inst_1557_, v_inst_1558_, v_f_1559_, v_a_u2081_1560_, v_a_u2082_1561_, v_a_u2083_1562_);
v___x_1567_ = lean_apply_4(v_toBind_1564_, lean_box(0), lean_box(0), v___x_1566_, v___f_1565_);
return v___x_1567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084(lean_object* v_m_1568_, lean_object* v_inst_1569_, lean_object* v_inst_1570_, lean_object* v_f_1571_, lean_object* v_a_u2081_1572_, lean_object* v_a_u2082_1573_, lean_object* v_a_u2083_1574_, lean_object* v_a_u2084_1575_){
_start:
{
lean_object* v___x_1576_; 
v___x_1576_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___redArg(v_inst_1569_, v_inst_1570_, v_f_1571_, v_a_u2081_1572_, v_a_u2082_1573_, v_a_u2083_1574_, v_a_u2084_1575_);
return v___x_1576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2085___redArg___lam__0(lean_object* v_inst_1577_, lean_object* v_inst_1578_, lean_object* v_a_u2085_1579_, lean_object* v_____do__lift_1580_){
_start:
{
lean_object* v___x_1581_; 
v___x_1581_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1577_, v_inst_1578_, v_____do__lift_1580_, v_a_u2085_1579_);
return v___x_1581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2085___redArg(lean_object* v_inst_1582_, lean_object* v_inst_1583_, lean_object* v_f_1584_, lean_object* v_a_u2081_1585_, lean_object* v_a_u2082_1586_, lean_object* v_a_u2083_1587_, lean_object* v_a_u2084_1588_, lean_object* v_a_u2085_1589_){
_start:
{
lean_object* v_toBind_1590_; lean_object* v___f_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; 
v_toBind_1590_ = lean_ctor_get(v_inst_1583_, 1);
lean_inc(v_toBind_1590_);
lean_inc_ref(v_inst_1583_);
lean_inc_ref(v_inst_1582_);
v___f_1591_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2085___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1591_, 0, v_inst_1582_);
lean_closure_set(v___f_1591_, 1, v_inst_1583_);
lean_closure_set(v___f_1591_, 2, v_a_u2085_1589_);
v___x_1592_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___redArg(v_inst_1582_, v_inst_1583_, v_f_1584_, v_a_u2081_1585_, v_a_u2082_1586_, v_a_u2083_1587_, v_a_u2084_1588_);
v___x_1593_ = lean_apply_4(v_toBind_1590_, lean_box(0), lean_box(0), v___x_1592_, v___f_1591_);
return v___x_1593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2085(lean_object* v_m_1594_, lean_object* v_inst_1595_, lean_object* v_inst_1596_, lean_object* v_f_1597_, lean_object* v_a_u2081_1598_, lean_object* v_a_u2082_1599_, lean_object* v_a_u2083_1600_, lean_object* v_a_u2084_1601_, lean_object* v_a_u2085_1602_){
_start:
{
lean_object* v___x_1603_; 
v___x_1603_ = l_Lean_Meta_Sym_Internal_mkAppS_u2085___redArg(v_inst_1595_, v_inst_1596_, v_f_1597_, v_a_u2081_1598_, v_a_u2082_1599_, v_a_u2083_1600_, v_a_u2084_1601_, v_a_u2085_1602_);
return v___x_1603_;
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
