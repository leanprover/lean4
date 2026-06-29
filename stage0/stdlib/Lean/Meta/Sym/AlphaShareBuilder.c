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
size_t lean_usize_sub(size_t, size_t);
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
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__0;
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
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg(lean_object* v_x_86_, size_t v_x_87_, size_t v_x_88_, lean_object* v_x_89_, lean_object* v_x_90_){
_start:
{
if (lean_obj_tag(v_x_86_) == 0)
{
lean_object* v_es_91_; size_t v___x_92_; size_t v___x_93_; lean_object* v_j_94_; lean_object* v___x_95_; uint8_t v___x_96_; 
v_es_91_ = lean_ctor_get(v_x_86_, 0);
v___x_92_ = ((size_t)31ULL);
v___x_93_ = lean_usize_land(v_x_87_, v___x_92_);
v_j_94_ = lean_usize_to_nat(v___x_93_);
v___x_95_ = lean_array_get_size(v_es_91_);
v___x_96_ = lean_nat_dec_lt(v_j_94_, v___x_95_);
if (v___x_96_ == 0)
{
lean_dec(v_j_94_);
lean_dec(v_x_90_);
lean_dec_ref(v_x_89_);
return v_x_86_;
}
else
{
lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_135_; 
lean_inc_ref(v_es_91_);
v_isSharedCheck_135_ = !lean_is_exclusive(v_x_86_);
if (v_isSharedCheck_135_ == 0)
{
lean_object* v_unused_136_; 
v_unused_136_ = lean_ctor_get(v_x_86_, 0);
lean_dec(v_unused_136_);
v___x_98_ = v_x_86_;
v_isShared_99_ = v_isSharedCheck_135_;
goto v_resetjp_97_;
}
else
{
lean_dec(v_x_86_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_135_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v_v_100_; lean_object* v___x_101_; lean_object* v_xs_x27_102_; lean_object* v___y_104_; 
v_v_100_ = lean_array_fget(v_es_91_, v_j_94_);
v___x_101_ = lean_box(0);
v_xs_x27_102_ = lean_array_fset(v_es_91_, v_j_94_, v___x_101_);
switch(lean_obj_tag(v_v_100_))
{
case 0:
{
lean_object* v_key_109_; lean_object* v_val_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_120_; 
v_key_109_ = lean_ctor_get(v_v_100_, 0);
v_val_110_ = lean_ctor_get(v_v_100_, 1);
v_isSharedCheck_120_ = !lean_is_exclusive(v_v_100_);
if (v_isSharedCheck_120_ == 0)
{
v___x_112_ = v_v_100_;
v_isShared_113_ = v_isSharedCheck_120_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_val_110_);
lean_inc(v_key_109_);
lean_dec(v_v_100_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_120_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
uint8_t v___x_114_; 
lean_inc(v_key_109_);
lean_inc_ref(v_x_89_);
v___x_114_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_89_, v_key_109_);
if (v___x_114_ == 0)
{
lean_object* v___x_115_; lean_object* v___x_116_; 
lean_del_object(v___x_112_);
v___x_115_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_109_, v_val_110_, v_x_89_, v_x_90_);
v___x_116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_116_, 0, v___x_115_);
v___y_104_ = v___x_116_;
goto v___jp_103_;
}
else
{
lean_object* v___x_118_; 
lean_dec(v_val_110_);
lean_dec(v_key_109_);
if (v_isShared_113_ == 0)
{
lean_ctor_set(v___x_112_, 1, v_x_90_);
lean_ctor_set(v___x_112_, 0, v_x_89_);
v___x_118_ = v___x_112_;
goto v_reusejp_117_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v_x_89_);
lean_ctor_set(v_reuseFailAlloc_119_, 1, v_x_90_);
v___x_118_ = v_reuseFailAlloc_119_;
goto v_reusejp_117_;
}
v_reusejp_117_:
{
v___y_104_ = v___x_118_;
goto v___jp_103_;
}
}
}
}
case 1:
{
lean_object* v_node_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_133_; 
v_node_121_ = lean_ctor_get(v_v_100_, 0);
v_isSharedCheck_133_ = !lean_is_exclusive(v_v_100_);
if (v_isSharedCheck_133_ == 0)
{
v___x_123_ = v_v_100_;
v_isShared_124_ = v_isSharedCheck_133_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_node_121_);
lean_dec(v_v_100_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_133_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
size_t v___x_125_; size_t v___x_126_; size_t v___x_127_; size_t v___x_128_; lean_object* v___x_129_; lean_object* v___x_131_; 
v___x_125_ = ((size_t)5ULL);
v___x_126_ = lean_usize_shift_right(v_x_87_, v___x_125_);
v___x_127_ = ((size_t)1ULL);
v___x_128_ = lean_usize_add(v_x_88_, v___x_127_);
v___x_129_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg(v_node_121_, v___x_126_, v___x_128_, v_x_89_, v_x_90_);
if (v_isShared_124_ == 0)
{
lean_ctor_set(v___x_123_, 0, v___x_129_);
v___x_131_ = v___x_123_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v___x_129_);
v___x_131_ = v_reuseFailAlloc_132_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
v___y_104_ = v___x_131_;
goto v___jp_103_;
}
}
}
default: 
{
lean_object* v___x_134_; 
v___x_134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_134_, 0, v_x_89_);
lean_ctor_set(v___x_134_, 1, v_x_90_);
v___y_104_ = v___x_134_;
goto v___jp_103_;
}
}
v___jp_103_:
{
lean_object* v___x_105_; lean_object* v___x_107_; 
v___x_105_ = lean_array_fset(v_xs_x27_102_, v_j_94_, v___y_104_);
lean_dec(v_j_94_);
if (v_isShared_99_ == 0)
{
lean_ctor_set(v___x_98_, 0, v___x_105_);
v___x_107_ = v___x_98_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v___x_105_);
v___x_107_ = v_reuseFailAlloc_108_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
return v___x_107_;
}
}
}
}
}
else
{
lean_object* v_ks_137_; lean_object* v_vs_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_158_; 
v_ks_137_ = lean_ctor_get(v_x_86_, 0);
v_vs_138_ = lean_ctor_get(v_x_86_, 1);
v_isSharedCheck_158_ = !lean_is_exclusive(v_x_86_);
if (v_isSharedCheck_158_ == 0)
{
v___x_140_ = v_x_86_;
v_isShared_141_ = v_isSharedCheck_158_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_vs_138_);
lean_inc(v_ks_137_);
lean_dec(v_x_86_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_158_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___x_143_; 
if (v_isShared_141_ == 0)
{
v___x_143_ = v___x_140_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v_ks_137_);
lean_ctor_set(v_reuseFailAlloc_157_, 1, v_vs_138_);
v___x_143_ = v_reuseFailAlloc_157_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
lean_object* v_newNode_144_; uint8_t v___y_146_; size_t v___x_152_; uint8_t v___x_153_; 
v_newNode_144_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__3___redArg(v___x_143_, v_x_89_, v_x_90_);
v___x_152_ = ((size_t)7ULL);
v___x_153_ = lean_usize_dec_le(v___x_152_, v_x_88_);
if (v___x_153_ == 0)
{
lean_object* v___x_154_; lean_object* v___x_155_; uint8_t v___x_156_; 
v___x_154_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_144_);
v___x_155_ = lean_unsigned_to_nat(4u);
v___x_156_ = lean_nat_dec_lt(v___x_154_, v___x_155_);
lean_dec(v___x_154_);
v___y_146_ = v___x_156_;
goto v___jp_145_;
}
else
{
v___y_146_ = v___x_153_;
goto v___jp_145_;
}
v___jp_145_:
{
if (v___y_146_ == 0)
{
lean_object* v_ks_147_; lean_object* v_vs_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v_ks_147_ = lean_ctor_get(v_newNode_144_, 0);
lean_inc_ref(v_ks_147_);
v_vs_148_ = lean_ctor_get(v_newNode_144_, 1);
lean_inc_ref(v_vs_148_);
lean_dec_ref(v_newNode_144_);
v___x_149_ = lean_unsigned_to_nat(0u);
v___x_150_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__0);
v___x_151_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4___redArg(v_x_88_, v_ks_147_, v_vs_148_, v___x_149_, v___x_150_);
lean_dec_ref(v_vs_148_);
lean_dec_ref(v_ks_147_);
return v___x_151_;
}
else
{
return v_newNode_144_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4___redArg(size_t v_depth_159_, lean_object* v_keys_160_, lean_object* v_vals_161_, lean_object* v_i_162_, lean_object* v_entries_163_){
_start:
{
lean_object* v___x_164_; uint8_t v___x_165_; 
v___x_164_ = lean_array_get_size(v_keys_160_);
v___x_165_ = lean_nat_dec_lt(v_i_162_, v___x_164_);
if (v___x_165_ == 0)
{
lean_dec(v_i_162_);
return v_entries_163_;
}
else
{
lean_object* v_k_166_; lean_object* v_v_167_; uint64_t v___x_168_; size_t v_h_169_; size_t v___x_170_; lean_object* v___x_171_; size_t v___x_172_; size_t v___x_173_; size_t v___x_174_; size_t v_h_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v_k_166_ = lean_array_fget_borrowed(v_keys_160_, v_i_162_);
v_v_167_ = lean_array_fget_borrowed(v_vals_161_, v_i_162_);
v___x_168_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_k_166_);
v_h_169_ = lean_uint64_to_usize(v___x_168_);
v___x_170_ = ((size_t)5ULL);
v___x_171_ = lean_unsigned_to_nat(1u);
v___x_172_ = ((size_t)1ULL);
v___x_173_ = lean_usize_sub(v_depth_159_, v___x_172_);
v___x_174_ = lean_usize_mul(v___x_170_, v___x_173_);
v_h_175_ = lean_usize_shift_right(v_h_169_, v___x_174_);
v___x_176_ = lean_nat_add(v_i_162_, v___x_171_);
lean_dec(v_i_162_);
lean_inc(v_v_167_);
lean_inc(v_k_166_);
v___x_177_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg(v_entries_163_, v_h_175_, v_depth_159_, v_k_166_, v_v_167_);
v_i_162_ = v___x_176_;
v_entries_163_ = v___x_177_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_depth_179_, lean_object* v_keys_180_, lean_object* v_vals_181_, lean_object* v_i_182_, lean_object* v_entries_183_){
_start:
{
size_t v_depth_boxed_184_; lean_object* v_res_185_; 
v_depth_boxed_184_ = lean_unbox_usize(v_depth_179_);
lean_dec(v_depth_179_);
v_res_185_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4___redArg(v_depth_boxed_184_, v_keys_180_, v_vals_181_, v_i_182_, v_entries_183_);
lean_dec_ref(v_vals_181_);
lean_dec_ref(v_keys_180_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___boxed(lean_object* v_x_186_, lean_object* v_x_187_, lean_object* v_x_188_, lean_object* v_x_189_, lean_object* v_x_190_){
_start:
{
size_t v_x_2153__boxed_191_; size_t v_x_2154__boxed_192_; lean_object* v_res_193_; 
v_x_2153__boxed_191_ = lean_unbox_usize(v_x_187_);
lean_dec(v_x_187_);
v_x_2154__boxed_192_ = lean_unbox_usize(v_x_188_);
lean_dec(v_x_188_);
v_res_193_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg(v_x_186_, v_x_2153__boxed_191_, v_x_2154__boxed_192_, v_x_189_, v_x_190_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1___redArg(lean_object* v_x_194_, lean_object* v_x_195_, lean_object* v_x_196_){
_start:
{
uint64_t v___x_197_; size_t v___x_198_; size_t v___x_199_; lean_object* v___x_200_; 
v___x_197_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_195_);
v___x_198_ = lean_uint64_to_usize(v___x_197_);
v___x_199_ = ((size_t)1ULL);
v___x_200_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg(v_x_194_, v___x_198_, v___x_199_, v_x_195_, v_x_196_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0___redArg(lean_object* v_keys_201_, lean_object* v_i_202_, lean_object* v_k_203_, lean_object* v_k_u2080_204_){
_start:
{
lean_object* v___x_205_; uint8_t v___x_206_; 
v___x_205_ = lean_array_get_size(v_keys_201_);
v___x_206_ = lean_nat_dec_lt(v_i_202_, v___x_205_);
if (v___x_206_ == 0)
{
lean_dec_ref(v_k_203_);
lean_dec(v_i_202_);
lean_inc_ref(v_k_u2080_204_);
return v_k_u2080_204_;
}
else
{
lean_object* v_k_x27_207_; uint8_t v___x_208_; 
v_k_x27_207_ = lean_array_fget_borrowed(v_keys_201_, v_i_202_);
lean_inc(v_k_x27_207_);
lean_inc_ref(v_k_203_);
v___x_208_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_k_203_, v_k_x27_207_);
if (v___x_208_ == 0)
{
lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_209_ = lean_unsigned_to_nat(1u);
v___x_210_ = lean_nat_add(v_i_202_, v___x_209_);
lean_dec(v_i_202_);
v_i_202_ = v___x_210_;
goto _start;
}
else
{
lean_dec_ref(v_k_203_);
lean_dec(v_i_202_);
lean_inc(v_k_x27_207_);
return v_k_x27_207_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0___redArg___boxed(lean_object* v_keys_212_, lean_object* v_i_213_, lean_object* v_k_214_, lean_object* v_k_u2080_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0___redArg(v_keys_212_, v_i_213_, v_k_214_, v_k_u2080_215_);
lean_dec_ref(v_k_u2080_215_);
lean_dec_ref(v_keys_212_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg(lean_object* v_x_217_, size_t v_x_218_, lean_object* v_x_219_, lean_object* v_x_220_){
_start:
{
if (lean_obj_tag(v_x_217_) == 0)
{
lean_object* v_es_221_; lean_object* v___x_222_; size_t v___x_223_; size_t v___x_224_; lean_object* v_j_225_; lean_object* v___x_226_; 
v_es_221_ = lean_ctor_get(v_x_217_, 0);
lean_inc_ref(v_es_221_);
lean_dec_ref_known(v_x_217_, 1);
v___x_222_ = lean_box(2);
v___x_223_ = ((size_t)31ULL);
v___x_224_ = lean_usize_land(v_x_218_, v___x_223_);
v_j_225_ = lean_usize_to_nat(v___x_224_);
v___x_226_ = lean_array_get(v___x_222_, v_es_221_, v_j_225_);
lean_dec(v_j_225_);
lean_dec_ref(v_es_221_);
switch(lean_obj_tag(v___x_226_))
{
case 0:
{
lean_object* v_key_227_; uint8_t v___x_228_; 
v_key_227_ = lean_ctor_get(v___x_226_, 0);
lean_inc_n(v_key_227_, 2);
lean_dec_ref_known(v___x_226_, 2);
v___x_228_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_219_, v_key_227_);
if (v___x_228_ == 0)
{
lean_dec(v_key_227_);
lean_inc_ref(v_x_220_);
return v_x_220_;
}
else
{
return v_key_227_;
}
}
case 1:
{
lean_object* v_node_229_; size_t v___x_230_; size_t v___x_231_; 
v_node_229_ = lean_ctor_get(v___x_226_, 0);
lean_inc(v_node_229_);
lean_dec_ref_known(v___x_226_, 1);
v___x_230_ = ((size_t)5ULL);
v___x_231_ = lean_usize_shift_right(v_x_218_, v___x_230_);
v_x_217_ = v_node_229_;
v_x_218_ = v___x_231_;
goto _start;
}
default: 
{
lean_dec_ref(v_x_219_);
lean_inc_ref(v_x_220_);
return v_x_220_;
}
}
}
else
{
lean_object* v_ks_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v_ks_233_ = lean_ctor_get(v_x_217_, 0);
lean_inc_ref(v_ks_233_);
lean_dec_ref_known(v_x_217_, 2);
v___x_234_ = lean_unsigned_to_nat(0u);
v___x_235_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0___redArg(v_ks_233_, v___x_234_, v_x_219_, v_x_220_);
lean_dec_ref(v_ks_233_);
return v___x_235_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg___boxed(lean_object* v_x_236_, lean_object* v_x_237_, lean_object* v_x_238_, lean_object* v_x_239_){
_start:
{
size_t v_x_2335__boxed_240_; lean_object* v_res_241_; 
v_x_2335__boxed_240_ = lean_unbox_usize(v_x_237_);
lean_dec(v_x_237_);
v_res_241_ = l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg(v_x_236_, v_x_2335__boxed_240_, v_x_238_, v_x_239_);
lean_dec_ref(v_x_239_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object* v_e_242_, lean_object* v_a_243_){
_start:
{
lean_object* v___x_245_; lean_object* v_share_246_; lean_object* v___x_247_; uint64_t v___x_248_; size_t v___x_249_; lean_object* v___x_250_; uint8_t v___x_251_; 
v___x_245_ = lean_st_ref_get(v_a_243_);
v_share_246_ = lean_ctor_get(v___x_245_, 0);
lean_inc_ref(v_share_246_);
lean_dec(v___x_245_);
v___x_247_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy;
v___x_248_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_242_);
v___x_249_ = lean_uint64_to_usize(v___x_248_);
lean_inc_ref(v_e_242_);
v___x_250_ = l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg(v_share_246_, v___x_249_, v_e_242_, v___x_247_);
v___x_251_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_250_, v___x_247_);
if (v___x_251_ == 0)
{
lean_object* v___x_252_; 
lean_dec_ref(v_e_242_);
v___x_252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_252_, 0, v___x_250_);
return v___x_252_;
}
else
{
lean_object* v___x_253_; lean_object* v_share_254_; lean_object* v_maxFVar_255_; lean_object* v_proofInstInfo_256_; lean_object* v_inferType_257_; lean_object* v_getLevel_258_; lean_object* v_congrInfo_259_; lean_object* v_defEqI_260_; lean_object* v_extensions_261_; lean_object* v_issues_262_; lean_object* v_canon_263_; uint8_t v_debug_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_275_; 
lean_dec_ref(v___x_250_);
v___x_253_ = lean_st_ref_take(v_a_243_);
v_share_254_ = lean_ctor_get(v___x_253_, 0);
v_maxFVar_255_ = lean_ctor_get(v___x_253_, 1);
v_proofInstInfo_256_ = lean_ctor_get(v___x_253_, 2);
v_inferType_257_ = lean_ctor_get(v___x_253_, 3);
v_getLevel_258_ = lean_ctor_get(v___x_253_, 4);
v_congrInfo_259_ = lean_ctor_get(v___x_253_, 5);
v_defEqI_260_ = lean_ctor_get(v___x_253_, 6);
v_extensions_261_ = lean_ctor_get(v___x_253_, 7);
v_issues_262_ = lean_ctor_get(v___x_253_, 8);
v_canon_263_ = lean_ctor_get(v___x_253_, 9);
v_debug_264_ = lean_ctor_get_uint8(v___x_253_, sizeof(void*)*10);
v_isSharedCheck_275_ = !lean_is_exclusive(v___x_253_);
if (v_isSharedCheck_275_ == 0)
{
v___x_266_ = v___x_253_;
v_isShared_267_ = v_isSharedCheck_275_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_canon_263_);
lean_inc(v_issues_262_);
lean_inc(v_extensions_261_);
lean_inc(v_defEqI_260_);
lean_inc(v_congrInfo_259_);
lean_inc(v_getLevel_258_);
lean_inc(v_inferType_257_);
lean_inc(v_proofInstInfo_256_);
lean_inc(v_maxFVar_255_);
lean_inc(v_share_254_);
lean_dec(v___x_253_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_275_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_271_; 
v___x_268_ = lean_box(0);
lean_inc_ref(v_e_242_);
v___x_269_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1___redArg(v_share_254_, v_e_242_, v___x_268_);
if (v_isShared_267_ == 0)
{
lean_ctor_set(v___x_266_, 0, v___x_269_);
v___x_271_ = v___x_266_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v___x_269_);
lean_ctor_set(v_reuseFailAlloc_274_, 1, v_maxFVar_255_);
lean_ctor_set(v_reuseFailAlloc_274_, 2, v_proofInstInfo_256_);
lean_ctor_set(v_reuseFailAlloc_274_, 3, v_inferType_257_);
lean_ctor_set(v_reuseFailAlloc_274_, 4, v_getLevel_258_);
lean_ctor_set(v_reuseFailAlloc_274_, 5, v_congrInfo_259_);
lean_ctor_set(v_reuseFailAlloc_274_, 6, v_defEqI_260_);
lean_ctor_set(v_reuseFailAlloc_274_, 7, v_extensions_261_);
lean_ctor_set(v_reuseFailAlloc_274_, 8, v_issues_262_);
lean_ctor_set(v_reuseFailAlloc_274_, 9, v_canon_263_);
lean_ctor_set_uint8(v_reuseFailAlloc_274_, sizeof(void*)*10, v_debug_264_);
v___x_271_ = v_reuseFailAlloc_274_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_272_ = lean_st_ref_set(v_a_243_, v___x_271_);
v___x_273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_273_, 0, v_e_242_);
return v___x_273_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg___boxed(lean_object* v_e_276_, lean_object* v_a_277_, lean_object* v_a_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v_e_276_, v_a_277_);
lean_dec(v_a_277_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Sym_share1(lean_object* v_e_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_){
_start:
{
lean_object* v___x_288_; 
v___x_288_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v_e_280_, v_a_282_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___boxed(lean_object* v_e_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Lean_Meta_Sym_Internal_Sym_share1(v_e_289_, v_a_290_, v_a_291_, v_a_292_, v_a_293_, v_a_294_, v_a_295_);
lean_dec(v_a_295_);
lean_dec_ref(v_a_294_);
lean_dec(v_a_293_);
lean_dec_ref(v_a_292_);
lean_dec(v_a_291_);
lean_dec_ref(v_a_290_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0(lean_object* v_00_u03b2_298_, lean_object* v_x_299_, size_t v_x_300_, lean_object* v_x_301_, lean_object* v_x_302_){
_start:
{
lean_object* v___x_303_; 
v___x_303_ = l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg(v_x_299_, v_x_300_, v_x_301_, v_x_302_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___boxed(lean_object* v_00_u03b2_304_, lean_object* v_x_305_, lean_object* v_x_306_, lean_object* v_x_307_, lean_object* v_x_308_){
_start:
{
size_t v_x_2423__boxed_309_; lean_object* v_res_310_; 
v_x_2423__boxed_309_ = lean_unbox_usize(v_x_306_);
lean_dec(v_x_306_);
v_res_310_ = l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0(v_00_u03b2_304_, v_x_305_, v_x_2423__boxed_309_, v_x_307_, v_x_308_);
lean_dec_ref(v_x_308_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1(lean_object* v_00_u03b2_311_, lean_object* v_x_312_, lean_object* v_x_313_, lean_object* v_x_314_){
_start:
{
lean_object* v___x_315_; 
v___x_315_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1___redArg(v_x_312_, v_x_313_, v_x_314_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0(lean_object* v_00_u03b2_316_, lean_object* v_keys_317_, lean_object* v_vals_318_, lean_object* v_heq_319_, lean_object* v_i_320_, lean_object* v_k_321_, lean_object* v_k_u2080_322_){
_start:
{
lean_object* v___x_323_; 
v___x_323_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0___redArg(v_keys_317_, v_i_320_, v_k_321_, v_k_u2080_322_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0___boxed(lean_object* v_00_u03b2_324_, lean_object* v_keys_325_, lean_object* v_vals_326_, lean_object* v_heq_327_, lean_object* v_i_328_, lean_object* v_k_329_, lean_object* v_k_u2080_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0(v_00_u03b2_324_, v_keys_325_, v_vals_326_, v_heq_327_, v_i_328_, v_k_329_, v_k_u2080_330_);
lean_dec_ref(v_k_u2080_330_);
lean_dec_ref(v_vals_326_);
lean_dec_ref(v_keys_325_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2(lean_object* v_00_u03b2_332_, lean_object* v_x_333_, size_t v_x_334_, size_t v_x_335_, lean_object* v_x_336_, lean_object* v_x_337_){
_start:
{
lean_object* v___x_338_; 
v___x_338_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg(v_x_333_, v_x_334_, v_x_335_, v_x_336_, v_x_337_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_339_, lean_object* v_x_340_, lean_object* v_x_341_, lean_object* v_x_342_, lean_object* v_x_343_, lean_object* v_x_344_){
_start:
{
size_t v_x_2447__boxed_345_; size_t v_x_2448__boxed_346_; lean_object* v_res_347_; 
v_x_2447__boxed_345_ = lean_unbox_usize(v_x_341_);
lean_dec(v_x_341_);
v_x_2448__boxed_346_ = lean_unbox_usize(v_x_342_);
lean_dec(v_x_342_);
v_res_347_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2(v_00_u03b2_339_, v_x_340_, v_x_2447__boxed_345_, v_x_2448__boxed_346_, v_x_343_, v_x_344_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_348_, lean_object* v_n_349_, lean_object* v_k_350_, lean_object* v_v_351_){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__3___redArg(v_n_349_, v_k_350_, v_v_351_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_353_, size_t v_depth_354_, lean_object* v_keys_355_, lean_object* v_vals_356_, lean_object* v_heq_357_, lean_object* v_i_358_, lean_object* v_entries_359_){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4___redArg(v_depth_354_, v_keys_355_, v_vals_356_, v_i_358_, v_entries_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_361_, lean_object* v_depth_362_, lean_object* v_keys_363_, lean_object* v_vals_364_, lean_object* v_heq_365_, lean_object* v_i_366_, lean_object* v_entries_367_){
_start:
{
size_t v_depth_boxed_368_; lean_object* v_res_369_; 
v_depth_boxed_368_ = lean_unbox_usize(v_depth_362_);
lean_dec(v_depth_362_);
v_res_369_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4(v_00_u03b2_361_, v_depth_boxed_368_, v_keys_363_, v_vals_364_, v_heq_365_, v_i_366_, v_entries_367_);
lean_dec_ref(v_vals_364_);
lean_dec_ref(v_keys_363_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_370_, lean_object* v_x_371_, lean_object* v_x_372_, lean_object* v_x_373_, lean_object* v_x_374_){
_start:
{
lean_object* v___x_375_; 
v___x_375_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__3_spec__4___redArg(v_x_371_, v_x_372_, v_x_373_, v_x_374_);
return v___x_375_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0(void){
_start:
{
lean_object* v___x_376_; 
v___x_376_ = l_Lean_Meta_Sym_instInhabitedSymM(lean_box(0));
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0(lean_object* v_msg_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_){
_start:
{
lean_object* v___x_385_; lean_object* v___x_756__overap_386_; lean_object* v___x_387_; 
v___x_385_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0, &l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0);
v___x_756__overap_386_ = lean_panic_fn_borrowed(v___x_385_, v_msg_377_);
lean_inc(v___y_383_);
lean_inc_ref(v___y_382_);
lean_inc(v___y_381_);
lean_inc_ref(v___y_380_);
lean_inc(v___y_379_);
lean_inc_ref(v___y_378_);
v___x_387_ = lean_apply_7(v___x_756__overap_386_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, lean_box(0));
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___boxed(lean_object* v_msg_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0(v_msg_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_);
lean_dec(v___y_394_);
lean_dec_ref(v___y_393_);
lean_dec(v___y_392_);
lean_dec_ref(v___y_391_);
lean_dec(v___y_390_);
lean_dec_ref(v___y_389_);
return v_res_396_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__3(void){
_start:
{
lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_400_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__2));
v___x_401_ = lean_unsigned_to_nat(2u);
v___x_402_ = lean_unsigned_to_nat(42u);
v___x_403_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__1));
v___x_404_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_405_ = l_mkPanicMessageWithDecl(v___x_404_, v___x_403_, v___x_402_, v___x_401_, v___x_400_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object* v_e_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_){
_start:
{
lean_object* v___x_414_; lean_object* v_share_415_; lean_object* v___x_416_; uint64_t v___x_417_; size_t v___x_418_; lean_object* v___x_419_; uint8_t v___x_420_; 
v___x_414_ = lean_st_ref_get(v_a_408_);
v_share_415_ = lean_ctor_get(v___x_414_, 0);
lean_inc_ref(v_share_415_);
lean_dec(v___x_414_);
v___x_416_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy;
v___x_417_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_406_);
v___x_418_ = lean_uint64_to_usize(v___x_417_);
lean_inc_ref(v_e_406_);
v___x_419_ = l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg(v_share_415_, v___x_418_, v_e_406_, v___x_416_);
v___x_420_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_419_, v_e_406_);
lean_dec_ref(v_e_406_);
lean_dec_ref(v___x_419_);
if (v___x_420_ == 0)
{
lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_421_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__3, &l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__3_once, _init_l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__3);
v___x_422_ = l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0(v___x_421_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_);
return v___x_422_;
}
else
{
lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_423_ = lean_box(0);
v___x_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_424_, 0, v___x_423_);
return v___x_424_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared___boxed(lean_object* v_e_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_e_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_);
lean_dec(v_a_431_);
lean_dec_ref(v_a_430_);
lean_dec(v_a_429_);
lean_dec_ref(v_a_428_);
lean_dec(v_a_427_);
lean_dec_ref(v_a_426_);
return v_res_433_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2(void){
_start:
{
lean_object* v___f_444_; lean_object* v___f_445_; lean_object* v___x_446_; 
v___f_444_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__1));
v___f_445_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__0));
v___x_446_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___f_445_, v___f_444_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM___redArg(lean_object* v_k_447_, lean_object* v_a_448_){
_start:
{
lean_object* v___x_450_; lean_object* v_share_451_; lean_object* v_maxFVar_452_; lean_object* v_proofInstInfo_453_; lean_object* v_inferType_454_; lean_object* v_getLevel_455_; lean_object* v_congrInfo_456_; lean_object* v_defEqI_457_; lean_object* v_extensions_458_; lean_object* v_issues_459_; lean_object* v_canon_460_; uint8_t v_debug_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_497_; 
v___x_450_ = lean_st_ref_take(v_a_448_);
v_share_451_ = lean_ctor_get(v___x_450_, 0);
v_maxFVar_452_ = lean_ctor_get(v___x_450_, 1);
v_proofInstInfo_453_ = lean_ctor_get(v___x_450_, 2);
v_inferType_454_ = lean_ctor_get(v___x_450_, 3);
v_getLevel_455_ = lean_ctor_get(v___x_450_, 4);
v_congrInfo_456_ = lean_ctor_get(v___x_450_, 5);
v_defEqI_457_ = lean_ctor_get(v___x_450_, 6);
v_extensions_458_ = lean_ctor_get(v___x_450_, 7);
v_issues_459_ = lean_ctor_get(v___x_450_, 8);
v_canon_460_ = lean_ctor_get(v___x_450_, 9);
v_debug_461_ = lean_ctor_get_uint8(v___x_450_, sizeof(void*)*10);
v_isSharedCheck_497_ = !lean_is_exclusive(v___x_450_);
if (v_isSharedCheck_497_ == 0)
{
v___x_463_ = v___x_450_;
v_isShared_464_ = v_isSharedCheck_497_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_canon_460_);
lean_inc(v_issues_459_);
lean_inc(v_extensions_458_);
lean_inc(v_defEqI_457_);
lean_inc(v_congrInfo_456_);
lean_inc(v_getLevel_455_);
lean_inc(v_inferType_454_);
lean_inc(v_proofInstInfo_453_);
lean_inc(v_maxFVar_452_);
lean_inc(v_share_451_);
lean_dec(v___x_450_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_497_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_465_; lean_object* v___x_467_; 
v___x_465_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2, &l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2_once, _init_l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2);
if (v_isShared_464_ == 0)
{
lean_ctor_set(v___x_463_, 0, v___x_465_);
v___x_467_ = v___x_463_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v___x_465_);
lean_ctor_set(v_reuseFailAlloc_496_, 1, v_maxFVar_452_);
lean_ctor_set(v_reuseFailAlloc_496_, 2, v_proofInstInfo_453_);
lean_ctor_set(v_reuseFailAlloc_496_, 3, v_inferType_454_);
lean_ctor_set(v_reuseFailAlloc_496_, 4, v_getLevel_455_);
lean_ctor_set(v_reuseFailAlloc_496_, 5, v_congrInfo_456_);
lean_ctor_set(v_reuseFailAlloc_496_, 6, v_defEqI_457_);
lean_ctor_set(v_reuseFailAlloc_496_, 7, v_extensions_458_);
lean_ctor_set(v_reuseFailAlloc_496_, 8, v_issues_459_);
lean_ctor_set(v_reuseFailAlloc_496_, 9, v_canon_460_);
lean_ctor_set_uint8(v_reuseFailAlloc_496_, sizeof(void*)*10, v_debug_461_);
v___x_467_ = v_reuseFailAlloc_496_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
lean_object* v___x_468_; lean_object* v___x_469_; uint8_t v_debug_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v_fst_473_; lean_object* v_snd_474_; lean_object* v___x_475_; lean_object* v_maxFVar_476_; lean_object* v_proofInstInfo_477_; lean_object* v_inferType_478_; lean_object* v_getLevel_479_; lean_object* v_congrInfo_480_; lean_object* v_defEqI_481_; lean_object* v_extensions_482_; lean_object* v_issues_483_; lean_object* v_canon_484_; uint8_t v_debug_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_494_; 
v___x_468_ = lean_st_ref_set(v_a_448_, v___x_467_);
v___x_469_ = lean_st_ref_get(v_a_448_);
v_debug_470_ = lean_ctor_get_uint8(v___x_469_, sizeof(void*)*10);
lean_dec(v___x_469_);
v___x_471_ = lean_box(v_debug_470_);
v___x_472_ = lean_apply_2(v_k_447_, v___x_471_, v_share_451_);
v_fst_473_ = lean_ctor_get(v___x_472_, 0);
lean_inc(v_fst_473_);
v_snd_474_ = lean_ctor_get(v___x_472_, 1);
lean_inc(v_snd_474_);
lean_dec_ref(v___x_472_);
v___x_475_ = lean_st_ref_take(v_a_448_);
v_maxFVar_476_ = lean_ctor_get(v___x_475_, 1);
v_proofInstInfo_477_ = lean_ctor_get(v___x_475_, 2);
v_inferType_478_ = lean_ctor_get(v___x_475_, 3);
v_getLevel_479_ = lean_ctor_get(v___x_475_, 4);
v_congrInfo_480_ = lean_ctor_get(v___x_475_, 5);
v_defEqI_481_ = lean_ctor_get(v___x_475_, 6);
v_extensions_482_ = lean_ctor_get(v___x_475_, 7);
v_issues_483_ = lean_ctor_get(v___x_475_, 8);
v_canon_484_ = lean_ctor_get(v___x_475_, 9);
v_debug_485_ = lean_ctor_get_uint8(v___x_475_, sizeof(void*)*10);
v_isSharedCheck_494_ = !lean_is_exclusive(v___x_475_);
if (v_isSharedCheck_494_ == 0)
{
lean_object* v_unused_495_; 
v_unused_495_ = lean_ctor_get(v___x_475_, 0);
lean_dec(v_unused_495_);
v___x_487_ = v___x_475_;
v_isShared_488_ = v_isSharedCheck_494_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_canon_484_);
lean_inc(v_issues_483_);
lean_inc(v_extensions_482_);
lean_inc(v_defEqI_481_);
lean_inc(v_congrInfo_480_);
lean_inc(v_getLevel_479_);
lean_inc(v_inferType_478_);
lean_inc(v_proofInstInfo_477_);
lean_inc(v_maxFVar_476_);
lean_dec(v___x_475_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_494_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v___x_490_; 
if (v_isShared_488_ == 0)
{
lean_ctor_set(v___x_487_, 0, v_snd_474_);
v___x_490_ = v___x_487_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v_snd_474_);
lean_ctor_set(v_reuseFailAlloc_493_, 1, v_maxFVar_476_);
lean_ctor_set(v_reuseFailAlloc_493_, 2, v_proofInstInfo_477_);
lean_ctor_set(v_reuseFailAlloc_493_, 3, v_inferType_478_);
lean_ctor_set(v_reuseFailAlloc_493_, 4, v_getLevel_479_);
lean_ctor_set(v_reuseFailAlloc_493_, 5, v_congrInfo_480_);
lean_ctor_set(v_reuseFailAlloc_493_, 6, v_defEqI_481_);
lean_ctor_set(v_reuseFailAlloc_493_, 7, v_extensions_482_);
lean_ctor_set(v_reuseFailAlloc_493_, 8, v_issues_483_);
lean_ctor_set(v_reuseFailAlloc_493_, 9, v_canon_484_);
lean_ctor_set_uint8(v_reuseFailAlloc_493_, sizeof(void*)*10, v_debug_485_);
v___x_490_ = v_reuseFailAlloc_493_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_491_ = lean_st_ref_set(v_a_448_, v___x_490_);
v___x_492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_492_, 0, v_fst_473_);
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
lean_object* v___x_511_; lean_object* v_share_512_; lean_object* v_maxFVar_513_; lean_object* v_proofInstInfo_514_; lean_object* v_inferType_515_; lean_object* v_getLevel_516_; lean_object* v_congrInfo_517_; lean_object* v_defEqI_518_; lean_object* v_extensions_519_; lean_object* v_issues_520_; lean_object* v_canon_521_; uint8_t v_debug_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_558_; 
v___x_511_ = lean_st_ref_take(v_a_505_);
v_share_512_ = lean_ctor_get(v___x_511_, 0);
v_maxFVar_513_ = lean_ctor_get(v___x_511_, 1);
v_proofInstInfo_514_ = lean_ctor_get(v___x_511_, 2);
v_inferType_515_ = lean_ctor_get(v___x_511_, 3);
v_getLevel_516_ = lean_ctor_get(v___x_511_, 4);
v_congrInfo_517_ = lean_ctor_get(v___x_511_, 5);
v_defEqI_518_ = lean_ctor_get(v___x_511_, 6);
v_extensions_519_ = lean_ctor_get(v___x_511_, 7);
v_issues_520_ = lean_ctor_get(v___x_511_, 8);
v_canon_521_ = lean_ctor_get(v___x_511_, 9);
v_debug_522_ = lean_ctor_get_uint8(v___x_511_, sizeof(void*)*10);
v_isSharedCheck_558_ = !lean_is_exclusive(v___x_511_);
if (v_isSharedCheck_558_ == 0)
{
v___x_524_ = v___x_511_;
v_isShared_525_ = v_isSharedCheck_558_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_canon_521_);
lean_inc(v_issues_520_);
lean_inc(v_extensions_519_);
lean_inc(v_defEqI_518_);
lean_inc(v_congrInfo_517_);
lean_inc(v_getLevel_516_);
lean_inc(v_inferType_515_);
lean_inc(v_proofInstInfo_514_);
lean_inc(v_maxFVar_513_);
lean_inc(v_share_512_);
lean_dec(v___x_511_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_558_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_526_; lean_object* v___x_528_; 
v___x_526_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2, &l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2_once, _init_l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2);
if (v_isShared_525_ == 0)
{
lean_ctor_set(v___x_524_, 0, v___x_526_);
v___x_528_ = v___x_524_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v___x_526_);
lean_ctor_set(v_reuseFailAlloc_557_, 1, v_maxFVar_513_);
lean_ctor_set(v_reuseFailAlloc_557_, 2, v_proofInstInfo_514_);
lean_ctor_set(v_reuseFailAlloc_557_, 3, v_inferType_515_);
lean_ctor_set(v_reuseFailAlloc_557_, 4, v_getLevel_516_);
lean_ctor_set(v_reuseFailAlloc_557_, 5, v_congrInfo_517_);
lean_ctor_set(v_reuseFailAlloc_557_, 6, v_defEqI_518_);
lean_ctor_set(v_reuseFailAlloc_557_, 7, v_extensions_519_);
lean_ctor_set(v_reuseFailAlloc_557_, 8, v_issues_520_);
lean_ctor_set(v_reuseFailAlloc_557_, 9, v_canon_521_);
lean_ctor_set_uint8(v_reuseFailAlloc_557_, sizeof(void*)*10, v_debug_522_);
v___x_528_ = v_reuseFailAlloc_557_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
lean_object* v___x_529_; lean_object* v___x_530_; uint8_t v_debug_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v_fst_534_; lean_object* v_snd_535_; lean_object* v___x_536_; lean_object* v_maxFVar_537_; lean_object* v_proofInstInfo_538_; lean_object* v_inferType_539_; lean_object* v_getLevel_540_; lean_object* v_congrInfo_541_; lean_object* v_defEqI_542_; lean_object* v_extensions_543_; lean_object* v_issues_544_; lean_object* v_canon_545_; uint8_t v_debug_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_555_; 
v___x_529_ = lean_st_ref_set(v_a_505_, v___x_528_);
v___x_530_ = lean_st_ref_get(v_a_505_);
v_debug_531_ = lean_ctor_get_uint8(v___x_530_, sizeof(void*)*10);
lean_dec(v___x_530_);
v___x_532_ = lean_box(v_debug_531_);
v___x_533_ = lean_apply_2(v_k_503_, v___x_532_, v_share_512_);
v_fst_534_ = lean_ctor_get(v___x_533_, 0);
lean_inc(v_fst_534_);
v_snd_535_ = lean_ctor_get(v___x_533_, 1);
lean_inc(v_snd_535_);
lean_dec_ref(v___x_533_);
v___x_536_ = lean_st_ref_take(v_a_505_);
v_maxFVar_537_ = lean_ctor_get(v___x_536_, 1);
v_proofInstInfo_538_ = lean_ctor_get(v___x_536_, 2);
v_inferType_539_ = lean_ctor_get(v___x_536_, 3);
v_getLevel_540_ = lean_ctor_get(v___x_536_, 4);
v_congrInfo_541_ = lean_ctor_get(v___x_536_, 5);
v_defEqI_542_ = lean_ctor_get(v___x_536_, 6);
v_extensions_543_ = lean_ctor_get(v___x_536_, 7);
v_issues_544_ = lean_ctor_get(v___x_536_, 8);
v_canon_545_ = lean_ctor_get(v___x_536_, 9);
v_debug_546_ = lean_ctor_get_uint8(v___x_536_, sizeof(void*)*10);
v_isSharedCheck_555_ = !lean_is_exclusive(v___x_536_);
if (v_isSharedCheck_555_ == 0)
{
lean_object* v_unused_556_; 
v_unused_556_ = lean_ctor_get(v___x_536_, 0);
lean_dec(v_unused_556_);
v___x_548_ = v___x_536_;
v_isShared_549_ = v_isSharedCheck_555_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_canon_545_);
lean_inc(v_issues_544_);
lean_inc(v_extensions_543_);
lean_inc(v_defEqI_542_);
lean_inc(v_congrInfo_541_);
lean_inc(v_getLevel_540_);
lean_inc(v_inferType_539_);
lean_inc(v_proofInstInfo_538_);
lean_inc(v_maxFVar_537_);
lean_dec(v___x_536_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_555_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v___x_551_; 
if (v_isShared_549_ == 0)
{
lean_ctor_set(v___x_548_, 0, v_snd_535_);
v___x_551_ = v___x_548_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_snd_535_);
lean_ctor_set(v_reuseFailAlloc_554_, 1, v_maxFVar_537_);
lean_ctor_set(v_reuseFailAlloc_554_, 2, v_proofInstInfo_538_);
lean_ctor_set(v_reuseFailAlloc_554_, 3, v_inferType_539_);
lean_ctor_set(v_reuseFailAlloc_554_, 4, v_getLevel_540_);
lean_ctor_set(v_reuseFailAlloc_554_, 5, v_congrInfo_541_);
lean_ctor_set(v_reuseFailAlloc_554_, 6, v_defEqI_542_);
lean_ctor_set(v_reuseFailAlloc_554_, 7, v_extensions_543_);
lean_ctor_set(v_reuseFailAlloc_554_, 8, v_issues_544_);
lean_ctor_set(v_reuseFailAlloc_554_, 9, v_canon_545_);
lean_ctor_set_uint8(v_reuseFailAlloc_554_, sizeof(void*)*10, v_debug_546_);
v___x_551_ = v_reuseFailAlloc_554_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_552_ = lean_st_ref_set(v_a_505_, v___x_551_);
v___x_553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_553_, 0, v_fst_534_);
return v___x_553_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM___boxed(lean_object* v_00_u03b1_559_, lean_object* v_k_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l_Lean_Meta_Sym_Internal_liftBuilderM(v_00_u03b1_559_, v_k_560_, v_a_561_, v_a_562_, v_a_563_, v_a_564_, v_a_565_, v_a_566_);
lean_dec(v_a_566_);
lean_dec_ref(v_a_565_);
lean_dec(v_a_564_);
lean_dec_ref(v_a_563_);
lean_dec(v_a_562_);
lean_dec_ref(v_a_561_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_share1___redArg(lean_object* v_e_569_, lean_object* v_a_570_){
_start:
{
lean_object* v___x_571_; uint64_t v___x_572_; size_t v___x_573_; lean_object* v___x_574_; uint8_t v___x_575_; 
v___x_571_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy;
v___x_572_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_569_);
v___x_573_ = lean_uint64_to_usize(v___x_572_);
lean_inc_ref(v_e_569_);
lean_inc_ref(v_a_570_);
v___x_574_ = l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg(v_a_570_, v___x_573_, v_e_569_, v___x_571_);
v___x_575_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_574_, v___x_571_);
if (v___x_575_ == 0)
{
lean_object* v___x_576_; 
lean_dec_ref(v_e_569_);
v___x_576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_576_, 0, v___x_574_);
lean_ctor_set(v___x_576_, 1, v_a_570_);
return v___x_576_;
}
else
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
lean_dec_ref(v___x_574_);
v___x_577_ = lean_box(0);
lean_inc_ref(v_e_569_);
v___x_578_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1___redArg(v_a_570_, v_e_569_, v___x_577_);
v___x_579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_579_, 0, v_e_569_);
lean_ctor_set(v___x_579_, 1, v___x_578_);
return v___x_579_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_share1(lean_object* v_e_580_, uint8_t v_a_581_, lean_object* v_a_582_){
_start:
{
lean_object* v___x_583_; 
v___x_583_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v_e_580_, v_a_582_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_share1___boxed(lean_object* v_e_584_, lean_object* v_a_585_, lean_object* v_a_586_){
_start:
{
uint8_t v_a_boxed_587_; lean_object* v_res_588_; 
v_a_boxed_587_ = lean_unbox(v_a_585_);
v_res_588_ = l_Lean_Meta_Sym_Internal_Builder_share1(v_e_584_, v_a_boxed_587_, v_a_586_);
return v_res_588_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1(lean_object* v_msg_596_, uint8_t v___y_597_, lean_object* v___y_598_){
_start:
{
lean_object* v___f_599_; lean_object* v___f_600_; lean_object* v___f_601_; lean_object* v___f_602_; lean_object* v___f_603_; lean_object* v___f_604_; lean_object* v___f_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___f_609_; lean_object* v___f_610_; lean_object* v___f_611_; lean_object* v___f_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___f_621_; lean_object* v___x_692__overap_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v___f_599_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__0));
v___f_600_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__1));
v___f_601_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__2));
v___f_602_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__3));
v___f_603_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__4));
v___f_604_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__5));
v___f_605_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__6));
v___x_606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_606_, 0, v___f_599_);
lean_ctor_set(v___x_606_, 1, v___f_600_);
v___x_607_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_607_, 0, v___x_606_);
lean_ctor_set(v___x_607_, 1, v___f_601_);
lean_ctor_set(v___x_607_, 2, v___f_602_);
lean_ctor_set(v___x_607_, 3, v___f_603_);
lean_ctor_set(v___x_607_, 4, v___f_604_);
v___x_608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_608_, 0, v___x_607_);
lean_ctor_set(v___x_608_, 1, v___f_605_);
lean_inc_ref_n(v___x_608_, 6);
v___f_609_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_609_, 0, v___x_608_);
v___f_610_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_610_, 0, v___x_608_);
v___f_611_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_611_, 0, v___x_608_);
v___f_612_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_612_, 0, v___x_608_);
v___x_613_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_613_, 0, lean_box(0));
lean_closure_set(v___x_613_, 1, lean_box(0));
lean_closure_set(v___x_613_, 2, v___x_608_);
v___x_614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_614_, 0, v___x_613_);
lean_ctor_set(v___x_614_, 1, v___f_609_);
v___x_615_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_615_, 0, lean_box(0));
lean_closure_set(v___x_615_, 1, lean_box(0));
lean_closure_set(v___x_615_, 2, v___x_608_);
v___x_616_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_616_, 0, v___x_614_);
lean_ctor_set(v___x_616_, 1, v___x_615_);
lean_ctor_set(v___x_616_, 2, v___f_610_);
lean_ctor_set(v___x_616_, 3, v___f_611_);
lean_ctor_set(v___x_616_, 4, v___f_612_);
v___x_617_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_617_, 0, lean_box(0));
lean_closure_set(v___x_617_, 1, lean_box(0));
lean_closure_set(v___x_617_, 2, v___x_608_);
v___x_618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_618_, 0, v___x_616_);
lean_ctor_set(v___x_618_, 1, v___x_617_);
v___x_619_ = lean_box(0);
v___x_620_ = l_instInhabitedOfMonad___redArg(v___x_618_, v___x_619_);
v___f_621_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_621_, 0, v___x_620_);
v___x_692__overap_622_ = lean_panic_fn_borrowed(v___f_621_, v_msg_596_);
lean_dec_ref(v___f_621_);
v___x_623_ = lean_box(v___y_597_);
v___x_624_ = lean_apply_2(v___x_692__overap_622_, v___x_623_, v___y_598_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___boxed(lean_object* v_msg_625_, lean_object* v___y_626_, lean_object* v___y_627_){
_start:
{
uint8_t v___y_821__boxed_628_; lean_object* v_res_629_; 
v___y_821__boxed_628_ = lean_unbox(v___y_626_);
v_res_629_ = l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1(v_msg_625_, v___y_821__boxed_628_, v___y_627_);
return v_res_629_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_630_, lean_object* v_i_631_, lean_object* v_k_632_){
_start:
{
lean_object* v___x_633_; uint8_t v___x_634_; 
v___x_633_ = lean_array_get_size(v_keys_630_);
v___x_634_ = lean_nat_dec_lt(v_i_631_, v___x_633_);
if (v___x_634_ == 0)
{
lean_dec_ref(v_k_632_);
lean_dec(v_i_631_);
return v___x_634_;
}
else
{
lean_object* v_k_x27_635_; uint8_t v___x_636_; 
v_k_x27_635_ = lean_array_fget_borrowed(v_keys_630_, v_i_631_);
lean_inc(v_k_x27_635_);
lean_inc_ref(v_k_632_);
v___x_636_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_k_632_, v_k_x27_635_);
if (v___x_636_ == 0)
{
lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_637_ = lean_unsigned_to_nat(1u);
v___x_638_ = lean_nat_add(v_i_631_, v___x_637_);
lean_dec(v_i_631_);
v_i_631_ = v___x_638_;
goto _start;
}
else
{
lean_dec_ref(v_k_632_);
lean_dec(v_i_631_);
return v___x_636_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_640_, lean_object* v_i_641_, lean_object* v_k_642_){
_start:
{
uint8_t v_res_643_; lean_object* v_r_644_; 
v_res_643_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg(v_keys_640_, v_i_641_, v_k_642_);
lean_dec_ref(v_keys_640_);
v_r_644_ = lean_box(v_res_643_);
return v_r_644_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg(lean_object* v_x_645_, size_t v_x_646_, lean_object* v_x_647_){
_start:
{
if (lean_obj_tag(v_x_645_) == 0)
{
lean_object* v_es_648_; lean_object* v___x_649_; size_t v___x_650_; size_t v___x_651_; lean_object* v_j_652_; lean_object* v___x_653_; 
v_es_648_ = lean_ctor_get(v_x_645_, 0);
lean_inc_ref(v_es_648_);
lean_dec_ref_known(v_x_645_, 1);
v___x_649_ = lean_box(2);
v___x_650_ = ((size_t)31ULL);
v___x_651_ = lean_usize_land(v_x_646_, v___x_650_);
v_j_652_ = lean_usize_to_nat(v___x_651_);
v___x_653_ = lean_array_get(v___x_649_, v_es_648_, v_j_652_);
lean_dec(v_j_652_);
lean_dec_ref(v_es_648_);
switch(lean_obj_tag(v___x_653_))
{
case 0:
{
lean_object* v_key_654_; uint8_t v___x_655_; 
v_key_654_ = lean_ctor_get(v___x_653_, 0);
lean_inc(v_key_654_);
lean_dec_ref_known(v___x_653_, 2);
v___x_655_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_647_, v_key_654_);
return v___x_655_;
}
case 1:
{
lean_object* v_node_656_; size_t v___x_657_; size_t v___x_658_; 
v_node_656_ = lean_ctor_get(v___x_653_, 0);
lean_inc(v_node_656_);
lean_dec_ref_known(v___x_653_, 1);
v___x_657_ = ((size_t)5ULL);
v___x_658_ = lean_usize_shift_right(v_x_646_, v___x_657_);
v_x_645_ = v_node_656_;
v_x_646_ = v___x_658_;
goto _start;
}
default: 
{
uint8_t v___x_660_; 
lean_dec_ref(v_x_647_);
v___x_660_ = 0;
return v___x_660_;
}
}
}
else
{
lean_object* v_ks_661_; lean_object* v___x_662_; uint8_t v___x_663_; 
v_ks_661_ = lean_ctor_get(v_x_645_, 0);
lean_inc_ref(v_ks_661_);
lean_dec_ref_known(v_x_645_, 2);
v___x_662_ = lean_unsigned_to_nat(0u);
v___x_663_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg(v_ks_661_, v___x_662_, v_x_647_);
lean_dec_ref(v_ks_661_);
return v___x_663_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg___boxed(lean_object* v_x_664_, lean_object* v_x_665_, lean_object* v_x_666_){
_start:
{
size_t v_x_897__boxed_667_; uint8_t v_res_668_; lean_object* v_r_669_; 
v_x_897__boxed_667_ = lean_unbox_usize(v_x_665_);
lean_dec(v_x_665_);
v_res_668_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg(v_x_664_, v_x_897__boxed_667_, v_x_666_);
v_r_669_ = lean_box(v_res_668_);
return v_r_669_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg(lean_object* v_x_670_, lean_object* v_x_671_){
_start:
{
uint64_t v___x_672_; size_t v___x_673_; uint8_t v___x_674_; 
v___x_672_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_671_);
v___x_673_ = lean_uint64_to_usize(v___x_672_);
v___x_674_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg(v_x_670_, v___x_673_, v_x_671_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg___boxed(lean_object* v_x_675_, lean_object* v_x_676_){
_start:
{
uint8_t v_res_677_; lean_object* v_r_678_; 
v_res_677_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg(v_x_675_, v_x_676_);
v_r_678_ = lean_box(v_res_677_);
return v_r_678_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__2(void){
_start:
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_681_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__1));
v___x_682_ = lean_unsigned_to_nat(2u);
v___x_683_ = lean_unsigned_to_nat(74u);
v___x_684_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__0));
v___x_685_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_686_ = l_mkPanicMessageWithDecl(v___x_685_, v___x_684_, v___x_683_, v___x_682_, v___x_681_);
return v___x_686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_assertShared(lean_object* v_e_687_, uint8_t v_a_688_, lean_object* v_a_689_){
_start:
{
uint8_t v___x_690_; 
lean_inc_ref(v_a_689_);
v___x_690_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg(v_a_689_, v_e_687_);
if (v___x_690_ == 0)
{
lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_691_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__2, &l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__2_once, _init_l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__2);
v___x_692_ = l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1(v___x_691_, v_a_688_, v_a_689_);
return v___x_692_;
}
else
{
lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_693_ = lean_box(0);
v___x_694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_694_, 0, v___x_693_);
lean_ctor_set(v___x_694_, 1, v_a_689_);
return v___x_694_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_assertShared___boxed(lean_object* v_e_695_, lean_object* v_a_696_, lean_object* v_a_697_){
_start:
{
uint8_t v_a_boxed_698_; lean_object* v_res_699_; 
v_a_boxed_698_ = lean_unbox(v_a_696_);
v_res_699_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_e_695_, v_a_boxed_698_, v_a_697_);
return v_res_699_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0(lean_object* v_00_u03b2_700_, lean_object* v_x_701_, lean_object* v_x_702_){
_start:
{
uint8_t v___x_703_; 
v___x_703_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg(v_x_701_, v_x_702_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___boxed(lean_object* v_00_u03b2_704_, lean_object* v_x_705_, lean_object* v_x_706_){
_start:
{
uint8_t v_res_707_; lean_object* v_r_708_; 
v_res_707_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0(v_00_u03b2_704_, v_x_705_, v_x_706_);
v_r_708_ = lean_box(v_res_707_);
return v_r_708_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0(lean_object* v_00_u03b2_709_, lean_object* v_x_710_, size_t v_x_711_, lean_object* v_x_712_){
_start:
{
uint8_t v___x_713_; 
v___x_713_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg(v_x_710_, v_x_711_, v_x_712_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___boxed(lean_object* v_00_u03b2_714_, lean_object* v_x_715_, lean_object* v_x_716_, lean_object* v_x_717_){
_start:
{
size_t v_x_996__boxed_718_; uint8_t v_res_719_; lean_object* v_r_720_; 
v_x_996__boxed_718_ = lean_unbox_usize(v_x_716_);
lean_dec(v_x_716_);
v_res_719_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0(v_00_u03b2_714_, v_x_715_, v_x_996__boxed_718_, v_x_717_);
v_r_720_ = lean_box(v_res_719_);
return v_r_720_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_721_, lean_object* v_keys_722_, lean_object* v_vals_723_, lean_object* v_heq_724_, lean_object* v_i_725_, lean_object* v_k_726_){
_start:
{
uint8_t v___x_727_; 
v___x_727_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg(v_keys_722_, v_i_725_, v_k_726_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_728_, lean_object* v_keys_729_, lean_object* v_vals_730_, lean_object* v_heq_731_, lean_object* v_i_732_, lean_object* v_k_733_){
_start:
{
uint8_t v_res_734_; lean_object* v_r_735_; 
v_res_734_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2(v_00_u03b2_728_, v_keys_729_, v_vals_730_, v_heq_731_, v_i_732_, v_k_733_);
lean_dec_ref(v_vals_730_);
lean_dec_ref(v_keys_729_);
v_r_735_ = lean_box(v_res_734_);
return v_r_735_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM(void){
_start:
{
lean_object* v___f_738_; lean_object* v___f_739_; lean_object* v___f_740_; lean_object* v___f_741_; lean_object* v___f_742_; lean_object* v___f_743_; lean_object* v___f_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___f_748_; lean_object* v___f_749_; lean_object* v___f_750_; lean_object* v___f_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v___f_738_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__0));
v___f_739_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__1));
v___f_740_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__2));
v___f_741_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__3));
v___f_742_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__4));
v___f_743_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__5));
v___f_744_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__6));
v___x_745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_745_, 0, v___f_738_);
lean_ctor_set(v___x_745_, 1, v___f_739_);
v___x_746_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_746_, 0, v___x_745_);
lean_ctor_set(v___x_746_, 1, v___f_740_);
lean_ctor_set(v___x_746_, 2, v___f_741_);
lean_ctor_set(v___x_746_, 3, v___f_742_);
lean_ctor_set(v___x_746_, 4, v___f_743_);
v___x_747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_747_, 0, v___x_746_);
lean_ctor_set(v___x_747_, 1, v___f_744_);
lean_inc_ref_n(v___x_747_, 6);
v___f_748_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_748_, 0, v___x_747_);
v___f_749_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_749_, 0, v___x_747_);
v___f_750_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_750_, 0, v___x_747_);
v___f_751_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_751_, 0, v___x_747_);
v___x_752_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_752_, 0, lean_box(0));
lean_closure_set(v___x_752_, 1, lean_box(0));
lean_closure_set(v___x_752_, 2, v___x_747_);
v___x_753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_753_, 0, v___x_752_);
lean_ctor_set(v___x_753_, 1, v___f_748_);
v___x_754_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_754_, 0, lean_box(0));
lean_closure_set(v___x_754_, 1, lean_box(0));
lean_closure_set(v___x_754_, 2, v___x_747_);
v___x_755_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_755_, 0, v___x_753_);
lean_ctor_set(v___x_755_, 1, v___x_754_);
lean_ctor_set(v___x_755_, 2, v___f_749_);
lean_ctor_set(v___x_755_, 3, v___f_750_);
lean_ctor_set(v___x_755_, 4, v___f_751_);
v___x_756_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_756_, 0, lean_box(0));
lean_closure_set(v___x_756_, 1, lean_box(0));
lean_closure_set(v___x_756_, 2, v___x_747_);
v___x_757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_757_, 0, v___x_755_);
lean_ctor_set(v___x_757_, 1, v___x_756_);
v___x_758_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__0));
v___x_759_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__1));
v___x_760_ = lean_alloc_closure((void*)(l_ReaderT_read___boxed), 4, 3);
lean_closure_set(v___x_760_, 0, lean_box(0));
lean_closure_set(v___x_760_, 1, lean_box(0));
lean_closure_set(v___x_760_, 2, v___x_757_);
v___x_761_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_761_, 0, v___x_758_);
lean_ctor_set(v___x_761_, 1, v___x_759_);
lean_ctor_set(v___x_761_, 2, v___x_760_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLitS___redArg(lean_object* v_inst_762_, lean_object* v_l_763_){
_start:
{
lean_object* v_share1_764_; lean_object* v___x_765_; lean_object* v___x_766_; 
v_share1_764_ = lean_ctor_get(v_inst_762_, 0);
lean_inc(v_share1_764_);
lean_dec_ref(v_inst_762_);
v___x_765_ = l_Lean_Expr_lit___override(v_l_763_);
v___x_766_ = lean_apply_1(v_share1_764_, v___x_765_);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLitS(lean_object* v_m_767_, lean_object* v_inst_768_, lean_object* v_l_769_){
_start:
{
lean_object* v___x_770_; 
v___x_770_ = l_Lean_Meta_Sym_Internal_mkLitS___redArg(v_inst_768_, v_l_769_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___redArg(lean_object* v_inst_771_, lean_object* v_declName_772_, lean_object* v_us_773_){
_start:
{
lean_object* v_share1_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
v_share1_774_ = lean_ctor_get(v_inst_771_, 0);
lean_inc(v_share1_774_);
lean_dec_ref(v_inst_771_);
v___x_775_ = l_Lean_Expr_const___override(v_declName_772_, v_us_773_);
v___x_776_ = lean_apply_1(v_share1_774_, v___x_775_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS(lean_object* v_m_777_, lean_object* v_inst_778_, lean_object* v_declName_779_, lean_object* v_us_780_){
_start:
{
lean_object* v___x_781_; 
v___x_781_ = l_Lean_Meta_Sym_Internal_mkConstS___redArg(v_inst_778_, v_declName_779_, v_us_780_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___redArg(lean_object* v_inst_782_, lean_object* v_idx_783_){
_start:
{
lean_object* v_share1_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
v_share1_784_ = lean_ctor_get(v_inst_782_, 0);
lean_inc(v_share1_784_);
lean_dec_ref(v_inst_782_);
v___x_785_ = l_Lean_Expr_bvar___override(v_idx_783_);
v___x_786_ = lean_apply_1(v_share1_784_, v___x_785_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS(lean_object* v_m_787_, lean_object* v_inst_788_, lean_object* v_idx_789_){
_start:
{
lean_object* v___x_790_; 
v___x_790_ = l_Lean_Meta_Sym_Internal_mkBVarS___redArg(v_inst_788_, v_idx_789_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS___redArg(lean_object* v_inst_791_, lean_object* v_u_792_){
_start:
{
lean_object* v_share1_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
v_share1_793_ = lean_ctor_get(v_inst_791_, 0);
lean_inc(v_share1_793_);
lean_dec_ref(v_inst_791_);
v___x_794_ = l_Lean_Expr_sort___override(v_u_792_);
v___x_795_ = lean_apply_1(v_share1_793_, v___x_794_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS(lean_object* v_m_796_, lean_object* v_inst_797_, lean_object* v_u_798_){
_start:
{
lean_object* v___x_799_; 
v___x_799_ = l_Lean_Meta_Sym_Internal_mkSortS___redArg(v_inst_797_, v_u_798_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___redArg(lean_object* v_inst_800_, lean_object* v_fvarId_801_){
_start:
{
lean_object* v_share1_802_; lean_object* v___x_803_; lean_object* v___x_804_; 
v_share1_802_ = lean_ctor_get(v_inst_800_, 0);
lean_inc(v_share1_802_);
lean_dec_ref(v_inst_800_);
v___x_803_ = l_Lean_Expr_fvar___override(v_fvarId_801_);
v___x_804_ = lean_apply_1(v_share1_802_, v___x_803_);
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS(lean_object* v_m_805_, lean_object* v_inst_806_, lean_object* v_fvarId_807_){
_start:
{
lean_object* v___x_808_; 
v___x_808_ = l_Lean_Meta_Sym_Internal_mkFVarS___redArg(v_inst_806_, v_fvarId_807_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMVarS___redArg(lean_object* v_inst_809_, lean_object* v_mvarId_810_){
_start:
{
lean_object* v_share1_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
v_share1_811_ = lean_ctor_get(v_inst_809_, 0);
lean_inc(v_share1_811_);
lean_dec_ref(v_inst_809_);
v___x_812_ = l_Lean_Expr_mvar___override(v_mvarId_810_);
v___x_813_ = lean_apply_1(v_share1_811_, v___x_812_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMVarS(lean_object* v_m_814_, lean_object* v_inst_815_, lean_object* v_mvarId_816_){
_start:
{
lean_object* v___x_817_; 
v___x_817_ = l_Lean_Meta_Sym_Internal_mkMVarS___redArg(v_inst_815_, v_mvarId_816_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__0(lean_object* v_d_818_, lean_object* v_e_819_, lean_object* v_share1_820_, lean_object* v_____r_821_){
_start:
{
lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_822_ = l_Lean_Expr_mdata___override(v_d_818_, v_e_819_);
v___x_823_ = lean_apply_1(v_share1_820_, v___x_822_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1(lean_object* v___f_824_, lean_object* v_____r_825_){
_start:
{
lean_object* v___x_826_; 
v___x_826_ = lean_apply_1(v___f_824_, v_____r_825_);
return v___x_826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__2(lean_object* v___f_827_, lean_object* v_assertShared_828_, lean_object* v_e_829_, lean_object* v_toBind_830_, lean_object* v___f_831_, uint8_t v_____do__lift_832_){
_start:
{
if (v_____do__lift_832_ == 0)
{
lean_object* v___x_833_; lean_object* v___x_834_; 
lean_dec(v___f_831_);
lean_dec(v_toBind_830_);
lean_dec_ref(v_e_829_);
lean_dec(v_assertShared_828_);
v___x_833_ = lean_box(0);
v___x_834_ = lean_apply_1(v___f_827_, v___x_833_);
return v___x_834_;
}
else
{
lean_object* v___x_835_; lean_object* v___x_836_; 
lean_dec(v___f_827_);
v___x_835_ = lean_apply_1(v_assertShared_828_, v_e_829_);
v___x_836_ = lean_apply_4(v_toBind_830_, lean_box(0), lean_box(0), v___x_835_, v___f_831_);
return v___x_836_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__2___boxed(lean_object* v___f_837_, lean_object* v_assertShared_838_, lean_object* v_e_839_, lean_object* v_toBind_840_, lean_object* v___f_841_, lean_object* v_____do__lift_842_){
_start:
{
uint8_t v_____do__lift_86__boxed_843_; lean_object* v_res_844_; 
v_____do__lift_86__boxed_843_ = lean_unbox(v_____do__lift_842_);
v_res_844_ = l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__2(v___f_837_, v_assertShared_838_, v_e_839_, v_toBind_840_, v___f_841_, v_____do__lift_86__boxed_843_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg(lean_object* v_inst_845_, lean_object* v_inst_846_, lean_object* v_d_847_, lean_object* v_e_848_){
_start:
{
lean_object* v_toBind_849_; lean_object* v_share1_850_; lean_object* v_assertShared_851_; lean_object* v_isDebugEnabled_852_; lean_object* v___f_853_; lean_object* v___f_854_; lean_object* v___f_855_; lean_object* v___x_856_; 
v_toBind_849_ = lean_ctor_get(v_inst_846_, 1);
lean_inc_n(v_toBind_849_, 2);
lean_dec_ref(v_inst_846_);
v_share1_850_ = lean_ctor_get(v_inst_845_, 0);
lean_inc(v_share1_850_);
v_assertShared_851_ = lean_ctor_get(v_inst_845_, 1);
lean_inc(v_assertShared_851_);
v_isDebugEnabled_852_ = lean_ctor_get(v_inst_845_, 2);
lean_inc(v_isDebugEnabled_852_);
lean_dec_ref(v_inst_845_);
lean_inc_ref(v_e_848_);
v___f_853_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__0), 4, 3);
lean_closure_set(v___f_853_, 0, v_d_847_);
lean_closure_set(v___f_853_, 1, v_e_848_);
lean_closure_set(v___f_853_, 2, v_share1_850_);
lean_inc_ref(v___f_853_);
v___f_854_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_854_, 0, v___f_853_);
v___f_855_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_855_, 0, v___f_853_);
lean_closure_set(v___f_855_, 1, v_assertShared_851_);
lean_closure_set(v___f_855_, 2, v_e_848_);
lean_closure_set(v___f_855_, 3, v_toBind_849_);
lean_closure_set(v___f_855_, 4, v___f_854_);
v___x_856_ = lean_apply_4(v_toBind_849_, lean_box(0), lean_box(0), v_isDebugEnabled_852_, v___f_855_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS(lean_object* v_m_857_, lean_object* v_inst_858_, lean_object* v_inst_859_, lean_object* v_d_860_, lean_object* v_e_861_){
_start:
{
lean_object* v___x_862_; 
v___x_862_ = l_Lean_Meta_Sym_Internal_mkMDataS___redArg(v_inst_858_, v_inst_859_, v_d_860_, v_e_861_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__0(lean_object* v_structName_863_, lean_object* v_idx_864_, lean_object* v_struct_865_, lean_object* v_share1_866_, lean_object* v_____r_867_){
_start:
{
lean_object* v___x_868_; lean_object* v___x_869_; 
v___x_868_ = l_Lean_Expr_proj___override(v_structName_863_, v_idx_864_, v_struct_865_);
v___x_869_ = lean_apply_1(v_share1_866_, v___x_868_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__2(lean_object* v___f_870_, lean_object* v_assertShared_871_, lean_object* v_struct_872_, lean_object* v_toBind_873_, lean_object* v___f_874_, uint8_t v_____do__lift_875_){
_start:
{
if (v_____do__lift_875_ == 0)
{
lean_object* v___x_876_; lean_object* v___x_877_; 
lean_dec(v___f_874_);
lean_dec(v_toBind_873_);
lean_dec_ref(v_struct_872_);
lean_dec(v_assertShared_871_);
v___x_876_ = lean_box(0);
v___x_877_ = lean_apply_1(v___f_870_, v___x_876_);
return v___x_877_;
}
else
{
lean_object* v___x_878_; lean_object* v___x_879_; 
lean_dec(v___f_870_);
v___x_878_ = lean_apply_1(v_assertShared_871_, v_struct_872_);
v___x_879_ = lean_apply_4(v_toBind_873_, lean_box(0), lean_box(0), v___x_878_, v___f_874_);
return v___x_879_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__2___boxed(lean_object* v___f_880_, lean_object* v_assertShared_881_, lean_object* v_struct_882_, lean_object* v_toBind_883_, lean_object* v___f_884_, lean_object* v_____do__lift_885_){
_start:
{
uint8_t v_____do__lift_80__boxed_886_; lean_object* v_res_887_; 
v_____do__lift_80__boxed_886_ = lean_unbox(v_____do__lift_885_);
v_res_887_ = l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__2(v___f_880_, v_assertShared_881_, v_struct_882_, v_toBind_883_, v___f_884_, v_____do__lift_80__boxed_886_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___redArg(lean_object* v_inst_888_, lean_object* v_inst_889_, lean_object* v_structName_890_, lean_object* v_idx_891_, lean_object* v_struct_892_){
_start:
{
lean_object* v_toBind_893_; lean_object* v_share1_894_; lean_object* v_assertShared_895_; lean_object* v_isDebugEnabled_896_; lean_object* v___f_897_; lean_object* v___f_898_; lean_object* v___f_899_; lean_object* v___x_900_; 
v_toBind_893_ = lean_ctor_get(v_inst_889_, 1);
lean_inc_n(v_toBind_893_, 2);
lean_dec_ref(v_inst_889_);
v_share1_894_ = lean_ctor_get(v_inst_888_, 0);
lean_inc(v_share1_894_);
v_assertShared_895_ = lean_ctor_get(v_inst_888_, 1);
lean_inc(v_assertShared_895_);
v_isDebugEnabled_896_ = lean_ctor_get(v_inst_888_, 2);
lean_inc(v_isDebugEnabled_896_);
lean_dec_ref(v_inst_888_);
lean_inc_ref(v_struct_892_);
v___f_897_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__0), 5, 4);
lean_closure_set(v___f_897_, 0, v_structName_890_);
lean_closure_set(v___f_897_, 1, v_idx_891_);
lean_closure_set(v___f_897_, 2, v_struct_892_);
lean_closure_set(v___f_897_, 3, v_share1_894_);
lean_inc_ref(v___f_897_);
v___f_898_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_898_, 0, v___f_897_);
v___f_899_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_899_, 0, v___f_897_);
lean_closure_set(v___f_899_, 1, v_assertShared_895_);
lean_closure_set(v___f_899_, 2, v_struct_892_);
lean_closure_set(v___f_899_, 3, v_toBind_893_);
lean_closure_set(v___f_899_, 4, v___f_898_);
v___x_900_ = lean_apply_4(v_toBind_893_, lean_box(0), lean_box(0), v_isDebugEnabled_896_, v___f_899_);
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS(lean_object* v_m_901_, lean_object* v_inst_902_, lean_object* v_inst_903_, lean_object* v_structName_904_, lean_object* v_idx_905_, lean_object* v_struct_906_){
_start:
{
lean_object* v___x_907_; 
v___x_907_ = l_Lean_Meta_Sym_Internal_mkProjS___redArg(v_inst_902_, v_inst_903_, v_structName_904_, v_idx_905_, v_struct_906_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__0(lean_object* v_f_908_, lean_object* v_a_909_, lean_object* v_share1_910_, lean_object* v_____r_911_){
_start:
{
lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_912_ = l_Lean_Expr_app___override(v_f_908_, v_a_909_);
v___x_913_ = lean_apply_1(v_share1_910_, v___x_912_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__2(lean_object* v_assertShared_914_, lean_object* v_a_915_, lean_object* v_toBind_916_, lean_object* v___f_917_, lean_object* v_____r_918_){
_start:
{
lean_object* v___x_919_; lean_object* v___x_920_; 
v___x_919_ = lean_apply_1(v_assertShared_914_, v_a_915_);
v___x_920_ = lean_apply_4(v_toBind_916_, lean_box(0), lean_box(0), v___x_919_, v___f_917_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__1(lean_object* v___f_921_, lean_object* v_assertShared_922_, lean_object* v_a_923_, lean_object* v_toBind_924_, lean_object* v___f_925_, lean_object* v_f_926_, uint8_t v_____do__lift_927_){
_start:
{
if (v_____do__lift_927_ == 0)
{
lean_object* v___x_928_; lean_object* v___x_929_; 
lean_dec_ref(v_f_926_);
lean_dec(v___f_925_);
lean_dec(v_toBind_924_);
lean_dec_ref(v_a_923_);
lean_dec(v_assertShared_922_);
v___x_928_ = lean_box(0);
v___x_929_ = lean_apply_1(v___f_921_, v___x_928_);
return v___x_929_;
}
else
{
lean_object* v___f_930_; lean_object* v___x_931_; lean_object* v___x_932_; 
lean_dec(v___f_921_);
lean_inc(v_toBind_924_);
lean_inc(v_assertShared_922_);
v___f_930_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__2), 5, 4);
lean_closure_set(v___f_930_, 0, v_assertShared_922_);
lean_closure_set(v___f_930_, 1, v_a_923_);
lean_closure_set(v___f_930_, 2, v_toBind_924_);
lean_closure_set(v___f_930_, 3, v___f_925_);
v___x_931_ = lean_apply_1(v_assertShared_922_, v_f_926_);
v___x_932_ = lean_apply_4(v_toBind_924_, lean_box(0), lean_box(0), v___x_931_, v___f_930_);
return v___x_932_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__1___boxed(lean_object* v___f_933_, lean_object* v_assertShared_934_, lean_object* v_a_935_, lean_object* v_toBind_936_, lean_object* v___f_937_, lean_object* v_f_938_, lean_object* v_____do__lift_939_){
_start:
{
uint8_t v_____do__lift_105__boxed_940_; lean_object* v_res_941_; 
v_____do__lift_105__boxed_940_ = lean_unbox(v_____do__lift_939_);
v_res_941_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__1(v___f_933_, v_assertShared_934_, v_a_935_, v_toBind_936_, v___f_937_, v_f_938_, v_____do__lift_105__boxed_940_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg(lean_object* v_inst_942_, lean_object* v_inst_943_, lean_object* v_f_944_, lean_object* v_a_945_){
_start:
{
lean_object* v_toBind_946_; lean_object* v_share1_947_; lean_object* v_assertShared_948_; lean_object* v_isDebugEnabled_949_; lean_object* v___f_950_; lean_object* v___f_951_; lean_object* v___f_952_; lean_object* v___x_953_; 
v_toBind_946_ = lean_ctor_get(v_inst_943_, 1);
lean_inc_n(v_toBind_946_, 2);
lean_dec_ref(v_inst_943_);
v_share1_947_ = lean_ctor_get(v_inst_942_, 0);
lean_inc(v_share1_947_);
v_assertShared_948_ = lean_ctor_get(v_inst_942_, 1);
lean_inc(v_assertShared_948_);
v_isDebugEnabled_949_ = lean_ctor_get(v_inst_942_, 2);
lean_inc(v_isDebugEnabled_949_);
lean_dec_ref(v_inst_942_);
lean_inc_ref(v_a_945_);
lean_inc_ref(v_f_944_);
v___f_950_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__0), 4, 3);
lean_closure_set(v___f_950_, 0, v_f_944_);
lean_closure_set(v___f_950_, 1, v_a_945_);
lean_closure_set(v___f_950_, 2, v_share1_947_);
lean_inc_ref(v___f_950_);
v___f_951_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_951_, 0, v___f_950_);
v___f_952_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_952_, 0, v___f_950_);
lean_closure_set(v___f_952_, 1, v_assertShared_948_);
lean_closure_set(v___f_952_, 2, v_a_945_);
lean_closure_set(v___f_952_, 3, v_toBind_946_);
lean_closure_set(v___f_952_, 4, v___f_951_);
lean_closure_set(v___f_952_, 5, v_f_944_);
v___x_953_ = lean_apply_4(v_toBind_946_, lean_box(0), lean_box(0), v_isDebugEnabled_949_, v___f_952_);
return v___x_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS(lean_object* v_m_954_, lean_object* v_inst_955_, lean_object* v_inst_956_, lean_object* v_f_957_, lean_object* v_a_958_){
_start:
{
lean_object* v___x_959_; 
v___x_959_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_955_, v_inst_956_, v_f_957_, v_a_958_);
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__0(lean_object* v_x_960_, lean_object* v_t_961_, lean_object* v_b_962_, uint8_t v_bi_963_, lean_object* v_share1_964_, lean_object* v_____r_965_){
_start:
{
lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_966_ = l_Lean_Expr_lam___override(v_x_960_, v_t_961_, v_b_962_, v_bi_963_);
v___x_967_ = lean_apply_1(v_share1_964_, v___x_966_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__0___boxed(lean_object* v_x_968_, lean_object* v_t_969_, lean_object* v_b_970_, lean_object* v_bi_971_, lean_object* v_share1_972_, lean_object* v_____r_973_){
_start:
{
uint8_t v_bi_boxed_974_; lean_object* v_res_975_; 
v_bi_boxed_974_ = lean_unbox(v_bi_971_);
v_res_975_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__0(v_x_968_, v_t_969_, v_b_970_, v_bi_boxed_974_, v_share1_972_, v_____r_973_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__2(lean_object* v_assertShared_976_, lean_object* v_b_977_, lean_object* v_toBind_978_, lean_object* v___f_979_, lean_object* v_____r_980_){
_start:
{
lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_981_ = lean_apply_1(v_assertShared_976_, v_b_977_);
v___x_982_ = lean_apply_4(v_toBind_978_, lean_box(0), lean_box(0), v___x_981_, v___f_979_);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1(lean_object* v___f_983_, lean_object* v_assertShared_984_, lean_object* v_b_985_, lean_object* v_toBind_986_, lean_object* v___f_987_, lean_object* v_t_988_, uint8_t v_____do__lift_989_){
_start:
{
if (v_____do__lift_989_ == 0)
{
lean_object* v___x_990_; lean_object* v___x_991_; 
lean_dec_ref(v_t_988_);
lean_dec(v___f_987_);
lean_dec(v_toBind_986_);
lean_dec_ref(v_b_985_);
lean_dec(v_assertShared_984_);
v___x_990_ = lean_box(0);
v___x_991_ = lean_apply_1(v___f_983_, v___x_990_);
return v___x_991_;
}
else
{
lean_object* v___f_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
lean_dec(v___f_983_);
lean_inc(v_toBind_986_);
lean_inc(v_assertShared_984_);
v___f_992_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__2), 5, 4);
lean_closure_set(v___f_992_, 0, v_assertShared_984_);
lean_closure_set(v___f_992_, 1, v_b_985_);
lean_closure_set(v___f_992_, 2, v_toBind_986_);
lean_closure_set(v___f_992_, 3, v___f_987_);
v___x_993_ = lean_apply_1(v_assertShared_984_, v_t_988_);
v___x_994_ = lean_apply_4(v_toBind_986_, lean_box(0), lean_box(0), v___x_993_, v___f_992_);
return v___x_994_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1___boxed(lean_object* v___f_995_, lean_object* v_assertShared_996_, lean_object* v_b_997_, lean_object* v_toBind_998_, lean_object* v___f_999_, lean_object* v_t_1000_, lean_object* v_____do__lift_1001_){
_start:
{
uint8_t v_____do__lift_106__boxed_1002_; lean_object* v_res_1003_; 
v_____do__lift_106__boxed_1002_ = lean_unbox(v_____do__lift_1001_);
v_res_1003_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1(v___f_995_, v_assertShared_996_, v_b_997_, v_toBind_998_, v___f_999_, v_t_1000_, v_____do__lift_106__boxed_1002_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(lean_object* v_inst_1004_, lean_object* v_inst_1005_, lean_object* v_x_1006_, uint8_t v_bi_1007_, lean_object* v_t_1008_, lean_object* v_b_1009_){
_start:
{
lean_object* v_toBind_1010_; lean_object* v_share1_1011_; lean_object* v_assertShared_1012_; lean_object* v_isDebugEnabled_1013_; lean_object* v___x_1014_; lean_object* v___f_1015_; lean_object* v___f_1016_; lean_object* v___f_1017_; lean_object* v___x_1018_; 
v_toBind_1010_ = lean_ctor_get(v_inst_1005_, 1);
lean_inc_n(v_toBind_1010_, 2);
lean_dec_ref(v_inst_1005_);
v_share1_1011_ = lean_ctor_get(v_inst_1004_, 0);
lean_inc(v_share1_1011_);
v_assertShared_1012_ = lean_ctor_get(v_inst_1004_, 1);
lean_inc(v_assertShared_1012_);
v_isDebugEnabled_1013_ = lean_ctor_get(v_inst_1004_, 2);
lean_inc(v_isDebugEnabled_1013_);
lean_dec_ref(v_inst_1004_);
v___x_1014_ = lean_box(v_bi_1007_);
lean_inc_ref(v_b_1009_);
lean_inc_ref(v_t_1008_);
v___f_1015_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1015_, 0, v_x_1006_);
lean_closure_set(v___f_1015_, 1, v_t_1008_);
lean_closure_set(v___f_1015_, 2, v_b_1009_);
lean_closure_set(v___f_1015_, 3, v___x_1014_);
lean_closure_set(v___f_1015_, 4, v_share1_1011_);
lean_inc_ref(v___f_1015_);
v___f_1016_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1016_, 0, v___f_1015_);
v___f_1017_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_1017_, 0, v___f_1015_);
lean_closure_set(v___f_1017_, 1, v_assertShared_1012_);
lean_closure_set(v___f_1017_, 2, v_b_1009_);
lean_closure_set(v___f_1017_, 3, v_toBind_1010_);
lean_closure_set(v___f_1017_, 4, v___f_1016_);
lean_closure_set(v___f_1017_, 5, v_t_1008_);
v___x_1018_ = lean_apply_4(v_toBind_1010_, lean_box(0), lean_box(0), v_isDebugEnabled_1013_, v___f_1017_);
return v___x_1018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___boxed(lean_object* v_inst_1019_, lean_object* v_inst_1020_, lean_object* v_x_1021_, lean_object* v_bi_1022_, lean_object* v_t_1023_, lean_object* v_b_1024_){
_start:
{
uint8_t v_bi_boxed_1025_; lean_object* v_res_1026_; 
v_bi_boxed_1025_ = lean_unbox(v_bi_1022_);
v_res_1026_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v_inst_1019_, v_inst_1020_, v_x_1021_, v_bi_boxed_1025_, v_t_1023_, v_b_1024_);
return v_res_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS(lean_object* v_m_1027_, lean_object* v_inst_1028_, lean_object* v_inst_1029_, lean_object* v_x_1030_, uint8_t v_bi_1031_, lean_object* v_t_1032_, lean_object* v_b_1033_){
_start:
{
lean_object* v___x_1034_; 
v___x_1034_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v_inst_1028_, v_inst_1029_, v_x_1030_, v_bi_1031_, v_t_1032_, v_b_1033_);
return v___x_1034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___boxed(lean_object* v_m_1035_, lean_object* v_inst_1036_, lean_object* v_inst_1037_, lean_object* v_x_1038_, lean_object* v_bi_1039_, lean_object* v_t_1040_, lean_object* v_b_1041_){
_start:
{
uint8_t v_bi_boxed_1042_; lean_object* v_res_1043_; 
v_bi_boxed_1042_ = lean_unbox(v_bi_1039_);
v_res_1043_ = l_Lean_Meta_Sym_Internal_mkLambdaS(v_m_1035_, v_inst_1036_, v_inst_1037_, v_x_1038_, v_bi_boxed_1042_, v_t_1040_, v_b_1041_);
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___redArg___lam__0(lean_object* v_x_1044_, lean_object* v_t_1045_, lean_object* v_b_1046_, uint8_t v_bi_1047_, lean_object* v_share1_1048_, lean_object* v_____r_1049_){
_start:
{
lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1050_ = l_Lean_Expr_forallE___override(v_x_1044_, v_t_1045_, v_b_1046_, v_bi_1047_);
v___x_1051_ = lean_apply_1(v_share1_1048_, v___x_1050_);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___redArg___lam__0___boxed(lean_object* v_x_1052_, lean_object* v_t_1053_, lean_object* v_b_1054_, lean_object* v_bi_1055_, lean_object* v_share1_1056_, lean_object* v_____r_1057_){
_start:
{
uint8_t v_bi_boxed_1058_; lean_object* v_res_1059_; 
v_bi_boxed_1058_ = lean_unbox(v_bi_1055_);
v_res_1059_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg___lam__0(v_x_1052_, v_t_1053_, v_b_1054_, v_bi_boxed_1058_, v_share1_1056_, v_____r_1057_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___redArg(lean_object* v_inst_1060_, lean_object* v_inst_1061_, lean_object* v_x_1062_, uint8_t v_bi_1063_, lean_object* v_t_1064_, lean_object* v_b_1065_){
_start:
{
lean_object* v_toBind_1066_; lean_object* v_share1_1067_; lean_object* v_assertShared_1068_; lean_object* v_isDebugEnabled_1069_; lean_object* v___x_1070_; lean_object* v___f_1071_; lean_object* v___f_1072_; lean_object* v___f_1073_; lean_object* v___x_1074_; 
v_toBind_1066_ = lean_ctor_get(v_inst_1061_, 1);
lean_inc_n(v_toBind_1066_, 2);
lean_dec_ref(v_inst_1061_);
v_share1_1067_ = lean_ctor_get(v_inst_1060_, 0);
lean_inc(v_share1_1067_);
v_assertShared_1068_ = lean_ctor_get(v_inst_1060_, 1);
lean_inc(v_assertShared_1068_);
v_isDebugEnabled_1069_ = lean_ctor_get(v_inst_1060_, 2);
lean_inc(v_isDebugEnabled_1069_);
lean_dec_ref(v_inst_1060_);
v___x_1070_ = lean_box(v_bi_1063_);
lean_inc_ref(v_b_1065_);
lean_inc_ref(v_t_1064_);
v___f_1071_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkForallS___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1071_, 0, v_x_1062_);
lean_closure_set(v___f_1071_, 1, v_t_1064_);
lean_closure_set(v___f_1071_, 2, v_b_1065_);
lean_closure_set(v___f_1071_, 3, v___x_1070_);
lean_closure_set(v___f_1071_, 4, v_share1_1067_);
lean_inc_ref(v___f_1071_);
v___f_1072_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1072_, 0, v___f_1071_);
v___f_1073_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_1073_, 0, v___f_1071_);
lean_closure_set(v___f_1073_, 1, v_assertShared_1068_);
lean_closure_set(v___f_1073_, 2, v_b_1065_);
lean_closure_set(v___f_1073_, 3, v_toBind_1066_);
lean_closure_set(v___f_1073_, 4, v___f_1072_);
lean_closure_set(v___f_1073_, 5, v_t_1064_);
v___x_1074_ = lean_apply_4(v_toBind_1066_, lean_box(0), lean_box(0), v_isDebugEnabled_1069_, v___f_1073_);
return v___x_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___redArg___boxed(lean_object* v_inst_1075_, lean_object* v_inst_1076_, lean_object* v_x_1077_, lean_object* v_bi_1078_, lean_object* v_t_1079_, lean_object* v_b_1080_){
_start:
{
uint8_t v_bi_boxed_1081_; lean_object* v_res_1082_; 
v_bi_boxed_1081_ = lean_unbox(v_bi_1078_);
v_res_1082_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v_inst_1075_, v_inst_1076_, v_x_1077_, v_bi_boxed_1081_, v_t_1079_, v_b_1080_);
return v_res_1082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS(lean_object* v_m_1083_, lean_object* v_inst_1084_, lean_object* v_inst_1085_, lean_object* v_x_1086_, uint8_t v_bi_1087_, lean_object* v_t_1088_, lean_object* v_b_1089_){
_start:
{
lean_object* v___x_1090_; 
v___x_1090_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v_inst_1084_, v_inst_1085_, v_x_1086_, v_bi_1087_, v_t_1088_, v_b_1089_);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___boxed(lean_object* v_m_1091_, lean_object* v_inst_1092_, lean_object* v_inst_1093_, lean_object* v_x_1094_, lean_object* v_bi_1095_, lean_object* v_t_1096_, lean_object* v_b_1097_){
_start:
{
uint8_t v_bi_boxed_1098_; lean_object* v_res_1099_; 
v_bi_boxed_1098_ = lean_unbox(v_bi_1095_);
v_res_1099_ = l_Lean_Meta_Sym_Internal_mkForallS(v_m_1091_, v_inst_1092_, v_inst_1093_, v_x_1094_, v_bi_boxed_1098_, v_t_1096_, v_b_1097_);
return v_res_1099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__0(lean_object* v_x_1100_, lean_object* v_t_1101_, lean_object* v_v_1102_, lean_object* v_b_1103_, uint8_t v_nondep_1104_, lean_object* v_share1_1105_, lean_object* v_____r_1106_){
_start:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___x_1107_ = l_Lean_Expr_letE___override(v_x_1100_, v_t_1101_, v_v_1102_, v_b_1103_, v_nondep_1104_);
v___x_1108_ = lean_apply_1(v_share1_1105_, v___x_1107_);
return v___x_1108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__0___boxed(lean_object* v_x_1109_, lean_object* v_t_1110_, lean_object* v_v_1111_, lean_object* v_b_1112_, lean_object* v_nondep_1113_, lean_object* v_share1_1114_, lean_object* v_____r_1115_){
_start:
{
uint8_t v_nondep_boxed_1116_; lean_object* v_res_1117_; 
v_nondep_boxed_1116_ = lean_unbox(v_nondep_1113_);
v_res_1117_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__0(v_x_1109_, v_t_1110_, v_v_1111_, v_b_1112_, v_nondep_boxed_1116_, v_share1_1114_, v_____r_1115_);
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__3(lean_object* v_assertShared_1118_, lean_object* v_v_1119_, lean_object* v_toBind_1120_, lean_object* v___f_1121_, lean_object* v_____r_1122_){
_start:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1123_ = lean_apply_1(v_assertShared_1118_, v_v_1119_);
v___x_1124_ = lean_apply_4(v_toBind_1120_, lean_box(0), lean_box(0), v___x_1123_, v___f_1121_);
return v___x_1124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1(lean_object* v___f_1125_, lean_object* v_assertShared_1126_, lean_object* v_b_1127_, lean_object* v_toBind_1128_, lean_object* v___f_1129_, lean_object* v_v_1130_, lean_object* v_t_1131_, uint8_t v_____do__lift_1132_){
_start:
{
if (v_____do__lift_1132_ == 0)
{
lean_object* v___x_1133_; lean_object* v___x_1134_; 
lean_dec_ref(v_t_1131_);
lean_dec_ref(v_v_1130_);
lean_dec(v___f_1129_);
lean_dec(v_toBind_1128_);
lean_dec_ref(v_b_1127_);
lean_dec(v_assertShared_1126_);
v___x_1133_ = lean_box(0);
v___x_1134_ = lean_apply_1(v___f_1125_, v___x_1133_);
return v___x_1134_;
}
else
{
lean_object* v___f_1135_; lean_object* v___f_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; 
lean_dec(v___f_1125_);
lean_inc_n(v_toBind_1128_, 2);
lean_inc_n(v_assertShared_1126_, 2);
v___f_1135_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__2), 5, 4);
lean_closure_set(v___f_1135_, 0, v_assertShared_1126_);
lean_closure_set(v___f_1135_, 1, v_b_1127_);
lean_closure_set(v___f_1135_, 2, v_toBind_1128_);
lean_closure_set(v___f_1135_, 3, v___f_1129_);
v___f_1136_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__3), 5, 4);
lean_closure_set(v___f_1136_, 0, v_assertShared_1126_);
lean_closure_set(v___f_1136_, 1, v_v_1130_);
lean_closure_set(v___f_1136_, 2, v_toBind_1128_);
lean_closure_set(v___f_1136_, 3, v___f_1135_);
v___x_1137_ = lean_apply_1(v_assertShared_1126_, v_t_1131_);
v___x_1138_ = lean_apply_4(v_toBind_1128_, lean_box(0), lean_box(0), v___x_1137_, v___f_1136_);
return v___x_1138_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1___boxed(lean_object* v___f_1139_, lean_object* v_assertShared_1140_, lean_object* v_b_1141_, lean_object* v_toBind_1142_, lean_object* v___f_1143_, lean_object* v_v_1144_, lean_object* v_t_1145_, lean_object* v_____do__lift_1146_){
_start:
{
uint8_t v_____do__lift_123__boxed_1147_; lean_object* v_res_1148_; 
v_____do__lift_123__boxed_1147_ = lean_unbox(v_____do__lift_1146_);
v_res_1148_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1(v___f_1139_, v_assertShared_1140_, v_b_1141_, v_toBind_1142_, v___f_1143_, v_v_1144_, v_t_1145_, v_____do__lift_123__boxed_1147_);
return v_res_1148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg(lean_object* v_inst_1149_, lean_object* v_inst_1150_, lean_object* v_x_1151_, lean_object* v_t_1152_, lean_object* v_v_1153_, lean_object* v_b_1154_, uint8_t v_nondep_1155_){
_start:
{
lean_object* v_toBind_1156_; lean_object* v_share1_1157_; lean_object* v_assertShared_1158_; lean_object* v_isDebugEnabled_1159_; lean_object* v___x_1160_; lean_object* v___f_1161_; lean_object* v___f_1162_; lean_object* v___f_1163_; lean_object* v___x_1164_; 
v_toBind_1156_ = lean_ctor_get(v_inst_1150_, 1);
lean_inc_n(v_toBind_1156_, 2);
lean_dec_ref(v_inst_1150_);
v_share1_1157_ = lean_ctor_get(v_inst_1149_, 0);
lean_inc(v_share1_1157_);
v_assertShared_1158_ = lean_ctor_get(v_inst_1149_, 1);
lean_inc(v_assertShared_1158_);
v_isDebugEnabled_1159_ = lean_ctor_get(v_inst_1149_, 2);
lean_inc(v_isDebugEnabled_1159_);
lean_dec_ref(v_inst_1149_);
v___x_1160_ = lean_box(v_nondep_1155_);
lean_inc_ref(v_b_1154_);
lean_inc_ref(v_v_1153_);
lean_inc_ref(v_t_1152_);
v___f_1161_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_1161_, 0, v_x_1151_);
lean_closure_set(v___f_1161_, 1, v_t_1152_);
lean_closure_set(v___f_1161_, 2, v_v_1153_);
lean_closure_set(v___f_1161_, 3, v_b_1154_);
lean_closure_set(v___f_1161_, 4, v___x_1160_);
lean_closure_set(v___f_1161_, 5, v_share1_1157_);
lean_inc_ref(v___f_1161_);
v___f_1162_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1162_, 0, v___f_1161_);
v___f_1163_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_1163_, 0, v___f_1161_);
lean_closure_set(v___f_1163_, 1, v_assertShared_1158_);
lean_closure_set(v___f_1163_, 2, v_b_1154_);
lean_closure_set(v___f_1163_, 3, v_toBind_1156_);
lean_closure_set(v___f_1163_, 4, v___f_1162_);
lean_closure_set(v___f_1163_, 5, v_v_1153_);
lean_closure_set(v___f_1163_, 6, v_t_1152_);
v___x_1164_ = lean_apply_4(v_toBind_1156_, lean_box(0), lean_box(0), v_isDebugEnabled_1159_, v___f_1163_);
return v___x_1164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___boxed(lean_object* v_inst_1165_, lean_object* v_inst_1166_, lean_object* v_x_1167_, lean_object* v_t_1168_, lean_object* v_v_1169_, lean_object* v_b_1170_, lean_object* v_nondep_1171_){
_start:
{
uint8_t v_nondep_boxed_1172_; lean_object* v_res_1173_; 
v_nondep_boxed_1172_ = lean_unbox(v_nondep_1171_);
v_res_1173_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1165_, v_inst_1166_, v_x_1167_, v_t_1168_, v_v_1169_, v_b_1170_, v_nondep_boxed_1172_);
return v_res_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS(lean_object* v_m_1174_, lean_object* v_inst_1175_, lean_object* v_inst_1176_, lean_object* v_x_1177_, lean_object* v_t_1178_, lean_object* v_v_1179_, lean_object* v_b_1180_, uint8_t v_nondep_1181_){
_start:
{
lean_object* v___x_1182_; 
v___x_1182_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1175_, v_inst_1176_, v_x_1177_, v_t_1178_, v_v_1179_, v_b_1180_, v_nondep_1181_);
return v___x_1182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___boxed(lean_object* v_m_1183_, lean_object* v_inst_1184_, lean_object* v_inst_1185_, lean_object* v_x_1186_, lean_object* v_t_1187_, lean_object* v_v_1188_, lean_object* v_b_1189_, lean_object* v_nondep_1190_){
_start:
{
uint8_t v_nondep_boxed_1191_; lean_object* v_res_1192_; 
v_nondep_boxed_1191_ = lean_unbox(v_nondep_1190_);
v_res_1192_ = l_Lean_Meta_Sym_Internal_mkLetS(v_m_1183_, v_inst_1184_, v_inst_1185_, v_x_1186_, v_t_1187_, v_v_1188_, v_b_1189_, v_nondep_boxed_1191_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkHaveS___redArg___lam__0(lean_object* v_x_1193_, lean_object* v_t_1194_, lean_object* v_v_1195_, lean_object* v_b_1196_, lean_object* v_share1_1197_, lean_object* v_____r_1198_){
_start:
{
uint8_t v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1199_ = 1;
v___x_1200_ = l_Lean_Expr_letE___override(v_x_1193_, v_t_1194_, v_v_1195_, v_b_1196_, v___x_1199_);
v___x_1201_ = lean_apply_1(v_share1_1197_, v___x_1200_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkHaveS___redArg(lean_object* v_inst_1202_, lean_object* v_inst_1203_, lean_object* v_x_1204_, lean_object* v_t_1205_, lean_object* v_v_1206_, lean_object* v_b_1207_){
_start:
{
lean_object* v_toBind_1208_; lean_object* v_share1_1209_; lean_object* v_assertShared_1210_; lean_object* v_isDebugEnabled_1211_; lean_object* v___f_1212_; lean_object* v___f_1213_; lean_object* v___f_1214_; lean_object* v___x_1215_; 
v_toBind_1208_ = lean_ctor_get(v_inst_1203_, 1);
lean_inc_n(v_toBind_1208_, 2);
lean_dec_ref(v_inst_1203_);
v_share1_1209_ = lean_ctor_get(v_inst_1202_, 0);
lean_inc(v_share1_1209_);
v_assertShared_1210_ = lean_ctor_get(v_inst_1202_, 1);
lean_inc(v_assertShared_1210_);
v_isDebugEnabled_1211_ = lean_ctor_get(v_inst_1202_, 2);
lean_inc(v_isDebugEnabled_1211_);
lean_dec_ref(v_inst_1202_);
lean_inc_ref(v_b_1207_);
lean_inc_ref(v_v_1206_);
lean_inc_ref(v_t_1205_);
v___f_1212_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkHaveS___redArg___lam__0), 6, 5);
lean_closure_set(v___f_1212_, 0, v_x_1204_);
lean_closure_set(v___f_1212_, 1, v_t_1205_);
lean_closure_set(v___f_1212_, 2, v_v_1206_);
lean_closure_set(v___f_1212_, 3, v_b_1207_);
lean_closure_set(v___f_1212_, 4, v_share1_1209_);
lean_inc_ref(v___f_1212_);
v___f_1213_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1213_, 0, v___f_1212_);
v___f_1214_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_1214_, 0, v___f_1212_);
lean_closure_set(v___f_1214_, 1, v_assertShared_1210_);
lean_closure_set(v___f_1214_, 2, v_b_1207_);
lean_closure_set(v___f_1214_, 3, v_toBind_1208_);
lean_closure_set(v___f_1214_, 4, v___f_1213_);
lean_closure_set(v___f_1214_, 5, v_v_1206_);
lean_closure_set(v___f_1214_, 6, v_t_1205_);
v___x_1215_ = lean_apply_4(v_toBind_1208_, lean_box(0), lean_box(0), v_isDebugEnabled_1211_, v___f_1214_);
return v___x_1215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkHaveS(lean_object* v_m_1216_, lean_object* v_inst_1217_, lean_object* v_inst_1218_, lean_object* v_x_1219_, lean_object* v_t_1220_, lean_object* v_v_1221_, lean_object* v_b_1222_){
_start:
{
lean_object* v___x_1223_; 
v___x_1223_ = l_Lean_Meta_Sym_Internal_mkHaveS___redArg(v_inst_1217_, v_inst_1218_, v_x_1219_, v_t_1220_, v_v_1221_, v_b_1222_);
return v___x_1223_;
}
}
static lean_object* _init_l_Lean_Expr_updateAppS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1226_ = ((lean_object*)(l_Lean_Expr_updateAppS_x21___redArg___closed__1));
v___x_1227_ = lean_unsigned_to_nat(25u);
v___x_1228_ = lean_unsigned_to_nat(148u);
v___x_1229_ = ((lean_object*)(l_Lean_Expr_updateAppS_x21___redArg___closed__0));
v___x_1230_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1231_ = l_mkPanicMessageWithDecl(v___x_1230_, v___x_1229_, v___x_1228_, v___x_1227_, v___x_1226_);
return v___x_1231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateAppS_x21___redArg(lean_object* v_inst_1232_, lean_object* v_inst_1233_, lean_object* v_e_1234_, lean_object* v_newFn_1235_, lean_object* v_newArg_1236_){
_start:
{
uint8_t v___y_1238_; 
if (lean_obj_tag(v_e_1234_) == 5)
{
lean_object* v_fn_1243_; lean_object* v_arg_1244_; uint8_t v___x_1245_; 
v_fn_1243_ = lean_ctor_get(v_e_1234_, 0);
v_arg_1244_ = lean_ctor_get(v_e_1234_, 1);
v___x_1245_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fn_1243_, v_newFn_1235_);
if (v___x_1245_ == 0)
{
v___y_1238_ = v___x_1245_;
goto v___jp_1237_;
}
else
{
uint8_t v___x_1246_; 
v___x_1246_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_1244_, v_newArg_1236_);
v___y_1238_ = v___x_1246_;
goto v___jp_1237_;
}
}
else
{
lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
lean_dec_ref(v_newArg_1236_);
lean_dec_ref(v_newFn_1235_);
lean_dec_ref(v_e_1234_);
lean_dec_ref(v_inst_1232_);
v___x_1247_ = l_Lean_instInhabitedExpr;
v___x_1248_ = l_instInhabitedOfMonad___redArg(v_inst_1233_, v___x_1247_);
v___x_1249_ = lean_obj_once(&l_Lean_Expr_updateAppS_x21___redArg___closed__2, &l_Lean_Expr_updateAppS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateAppS_x21___redArg___closed__2);
v___x_1250_ = l_panic___redArg(v___x_1248_, v___x_1249_);
lean_dec(v___x_1248_);
return v___x_1250_;
}
v___jp_1237_:
{
if (v___y_1238_ == 0)
{
lean_object* v___x_1239_; 
lean_dec_ref(v_e_1234_);
v___x_1239_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1232_, v_inst_1233_, v_newFn_1235_, v_newArg_1236_);
return v___x_1239_;
}
else
{
lean_object* v_toApplicative_1240_; lean_object* v_toPure_1241_; lean_object* v___x_1242_; 
lean_dec_ref(v_newArg_1236_);
lean_dec_ref(v_newFn_1235_);
lean_dec_ref(v_inst_1232_);
v_toApplicative_1240_ = lean_ctor_get(v_inst_1233_, 0);
lean_inc_ref(v_toApplicative_1240_);
lean_dec_ref(v_inst_1233_);
v_toPure_1241_ = lean_ctor_get(v_toApplicative_1240_, 1);
lean_inc(v_toPure_1241_);
lean_dec_ref(v_toApplicative_1240_);
v___x_1242_ = lean_apply_2(v_toPure_1241_, lean_box(0), v_e_1234_);
return v___x_1242_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateAppS_x21(lean_object* v_m_1251_, lean_object* v_inst_1252_, lean_object* v_inst_1253_, lean_object* v_e_1254_, lean_object* v_newFn_1255_, lean_object* v_newArg_1256_){
_start:
{
uint8_t v___y_1258_; 
if (lean_obj_tag(v_e_1254_) == 5)
{
lean_object* v_fn_1263_; lean_object* v_arg_1264_; uint8_t v___x_1265_; 
v_fn_1263_ = lean_ctor_get(v_e_1254_, 0);
v_arg_1264_ = lean_ctor_get(v_e_1254_, 1);
v___x_1265_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fn_1263_, v_newFn_1255_);
if (v___x_1265_ == 0)
{
v___y_1258_ = v___x_1265_;
goto v___jp_1257_;
}
else
{
uint8_t v___x_1266_; 
v___x_1266_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_1264_, v_newArg_1256_);
v___y_1258_ = v___x_1266_;
goto v___jp_1257_;
}
}
else
{
lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; 
lean_dec_ref(v_newArg_1256_);
lean_dec_ref(v_newFn_1255_);
lean_dec_ref(v_e_1254_);
lean_dec_ref(v_inst_1252_);
v___x_1267_ = l_Lean_instInhabitedExpr;
v___x_1268_ = l_instInhabitedOfMonad___redArg(v_inst_1253_, v___x_1267_);
v___x_1269_ = lean_obj_once(&l_Lean_Expr_updateAppS_x21___redArg___closed__2, &l_Lean_Expr_updateAppS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateAppS_x21___redArg___closed__2);
v___x_1270_ = l_panic___redArg(v___x_1268_, v___x_1269_);
lean_dec(v___x_1268_);
return v___x_1270_;
}
v___jp_1257_:
{
if (v___y_1258_ == 0)
{
lean_object* v___x_1259_; 
lean_dec_ref(v_e_1254_);
v___x_1259_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1252_, v_inst_1253_, v_newFn_1255_, v_newArg_1256_);
return v___x_1259_;
}
else
{
lean_object* v_toApplicative_1260_; lean_object* v_toPure_1261_; lean_object* v___x_1262_; 
lean_dec_ref(v_newArg_1256_);
lean_dec_ref(v_newFn_1255_);
lean_dec_ref(v_inst_1252_);
v_toApplicative_1260_ = lean_ctor_get(v_inst_1253_, 0);
lean_inc_ref(v_toApplicative_1260_);
lean_dec_ref(v_inst_1253_);
v_toPure_1261_ = lean_ctor_get(v_toApplicative_1260_, 1);
lean_inc(v_toPure_1261_);
lean_dec_ref(v_toApplicative_1260_);
v___x_1262_ = lean_apply_2(v_toPure_1261_, lean_box(0), v_e_1254_);
return v___x_1262_;
}
}
}
}
static lean_object* _init_l_Lean_Expr_updateMDataS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___x_1273_ = ((lean_object*)(l_Lean_Expr_updateMDataS_x21___redArg___closed__1));
v___x_1274_ = lean_unsigned_to_nat(24u);
v___x_1275_ = lean_unsigned_to_nat(152u);
v___x_1276_ = ((lean_object*)(l_Lean_Expr_updateMDataS_x21___redArg___closed__0));
v___x_1277_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1278_ = l_mkPanicMessageWithDecl(v___x_1277_, v___x_1276_, v___x_1275_, v___x_1274_, v___x_1273_);
return v___x_1278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateMDataS_x21___redArg(lean_object* v_inst_1279_, lean_object* v_inst_1280_, lean_object* v_e_1281_, lean_object* v_newExpr_1282_){
_start:
{
if (lean_obj_tag(v_e_1281_) == 10)
{
lean_object* v_data_1283_; lean_object* v_expr_1284_; uint8_t v___x_1285_; 
v_data_1283_ = lean_ctor_get(v_e_1281_, 0);
v_expr_1284_ = lean_ctor_get(v_e_1281_, 1);
v___x_1285_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_expr_1284_, v_newExpr_1282_);
if (v___x_1285_ == 0)
{
lean_object* v___x_1286_; 
lean_inc(v_data_1283_);
lean_dec_ref_known(v_e_1281_, 2);
v___x_1286_ = l_Lean_Meta_Sym_Internal_mkMDataS___redArg(v_inst_1279_, v_inst_1280_, v_data_1283_, v_newExpr_1282_);
return v___x_1286_;
}
else
{
lean_object* v_toApplicative_1287_; lean_object* v_toPure_1288_; lean_object* v___x_1289_; 
lean_dec_ref(v_newExpr_1282_);
lean_dec_ref(v_inst_1279_);
v_toApplicative_1287_ = lean_ctor_get(v_inst_1280_, 0);
lean_inc_ref(v_toApplicative_1287_);
lean_dec_ref(v_inst_1280_);
v_toPure_1288_ = lean_ctor_get(v_toApplicative_1287_, 1);
lean_inc(v_toPure_1288_);
lean_dec_ref(v_toApplicative_1287_);
v___x_1289_ = lean_apply_2(v_toPure_1288_, lean_box(0), v_e_1281_);
return v___x_1289_;
}
}
else
{
lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; 
lean_dec_ref(v_newExpr_1282_);
lean_dec_ref(v_e_1281_);
lean_dec_ref(v_inst_1279_);
v___x_1290_ = l_Lean_instInhabitedExpr;
v___x_1291_ = l_instInhabitedOfMonad___redArg(v_inst_1280_, v___x_1290_);
v___x_1292_ = lean_obj_once(&l_Lean_Expr_updateMDataS_x21___redArg___closed__2, &l_Lean_Expr_updateMDataS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateMDataS_x21___redArg___closed__2);
v___x_1293_ = l_panic___redArg(v___x_1291_, v___x_1292_);
lean_dec(v___x_1291_);
return v___x_1293_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateMDataS_x21(lean_object* v_m_1294_, lean_object* v_inst_1295_, lean_object* v_inst_1296_, lean_object* v_e_1297_, lean_object* v_newExpr_1298_){
_start:
{
if (lean_obj_tag(v_e_1297_) == 10)
{
lean_object* v_data_1299_; lean_object* v_expr_1300_; uint8_t v___x_1301_; 
v_data_1299_ = lean_ctor_get(v_e_1297_, 0);
v_expr_1300_ = lean_ctor_get(v_e_1297_, 1);
v___x_1301_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_expr_1300_, v_newExpr_1298_);
if (v___x_1301_ == 0)
{
lean_object* v___x_1302_; 
lean_inc(v_data_1299_);
lean_dec_ref_known(v_e_1297_, 2);
v___x_1302_ = l_Lean_Meta_Sym_Internal_mkMDataS___redArg(v_inst_1295_, v_inst_1296_, v_data_1299_, v_newExpr_1298_);
return v___x_1302_;
}
else
{
lean_object* v_toApplicative_1303_; lean_object* v_toPure_1304_; lean_object* v___x_1305_; 
lean_dec_ref(v_newExpr_1298_);
lean_dec_ref(v_inst_1295_);
v_toApplicative_1303_ = lean_ctor_get(v_inst_1296_, 0);
lean_inc_ref(v_toApplicative_1303_);
lean_dec_ref(v_inst_1296_);
v_toPure_1304_ = lean_ctor_get(v_toApplicative_1303_, 1);
lean_inc(v_toPure_1304_);
lean_dec_ref(v_toApplicative_1303_);
v___x_1305_ = lean_apply_2(v_toPure_1304_, lean_box(0), v_e_1297_);
return v___x_1305_;
}
}
else
{
lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
lean_dec_ref(v_newExpr_1298_);
lean_dec_ref(v_e_1297_);
lean_dec_ref(v_inst_1295_);
v___x_1306_ = l_Lean_instInhabitedExpr;
v___x_1307_ = l_instInhabitedOfMonad___redArg(v_inst_1296_, v___x_1306_);
v___x_1308_ = lean_obj_once(&l_Lean_Expr_updateMDataS_x21___redArg___closed__2, &l_Lean_Expr_updateMDataS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateMDataS_x21___redArg___closed__2);
v___x_1309_ = l_panic___redArg(v___x_1307_, v___x_1308_);
lean_dec(v___x_1307_);
return v___x_1309_;
}
}
}
static lean_object* _init_l_Lean_Expr_updateProjS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1312_ = ((lean_object*)(l_Lean_Expr_updateProjS_x21___redArg___closed__1));
v___x_1313_ = lean_unsigned_to_nat(25u);
v___x_1314_ = lean_unsigned_to_nat(156u);
v___x_1315_ = ((lean_object*)(l_Lean_Expr_updateProjS_x21___redArg___closed__0));
v___x_1316_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1317_ = l_mkPanicMessageWithDecl(v___x_1316_, v___x_1315_, v___x_1314_, v___x_1313_, v___x_1312_);
return v___x_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateProjS_x21___redArg(lean_object* v_inst_1318_, lean_object* v_inst_1319_, lean_object* v_e_1320_, lean_object* v_newExpr_1321_){
_start:
{
if (lean_obj_tag(v_e_1320_) == 11)
{
lean_object* v_typeName_1322_; lean_object* v_idx_1323_; lean_object* v_struct_1324_; uint8_t v___x_1325_; 
v_typeName_1322_ = lean_ctor_get(v_e_1320_, 0);
v_idx_1323_ = lean_ctor_get(v_e_1320_, 1);
v_struct_1324_ = lean_ctor_get(v_e_1320_, 2);
v___x_1325_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_1324_, v_newExpr_1321_);
if (v___x_1325_ == 0)
{
lean_object* v___x_1326_; 
lean_inc(v_idx_1323_);
lean_inc(v_typeName_1322_);
lean_dec_ref_known(v_e_1320_, 3);
v___x_1326_ = l_Lean_Meta_Sym_Internal_mkProjS___redArg(v_inst_1318_, v_inst_1319_, v_typeName_1322_, v_idx_1323_, v_newExpr_1321_);
return v___x_1326_;
}
else
{
lean_object* v_toApplicative_1327_; lean_object* v_toPure_1328_; lean_object* v___x_1329_; 
lean_dec_ref(v_newExpr_1321_);
lean_dec_ref(v_inst_1318_);
v_toApplicative_1327_ = lean_ctor_get(v_inst_1319_, 0);
lean_inc_ref(v_toApplicative_1327_);
lean_dec_ref(v_inst_1319_);
v_toPure_1328_ = lean_ctor_get(v_toApplicative_1327_, 1);
lean_inc(v_toPure_1328_);
lean_dec_ref(v_toApplicative_1327_);
v___x_1329_ = lean_apply_2(v_toPure_1328_, lean_box(0), v_e_1320_);
return v___x_1329_;
}
}
else
{
lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; 
lean_dec_ref(v_newExpr_1321_);
lean_dec_ref(v_e_1320_);
lean_dec_ref(v_inst_1318_);
v___x_1330_ = l_Lean_instInhabitedExpr;
v___x_1331_ = l_instInhabitedOfMonad___redArg(v_inst_1319_, v___x_1330_);
v___x_1332_ = lean_obj_once(&l_Lean_Expr_updateProjS_x21___redArg___closed__2, &l_Lean_Expr_updateProjS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateProjS_x21___redArg___closed__2);
v___x_1333_ = l_panic___redArg(v___x_1331_, v___x_1332_);
lean_dec(v___x_1331_);
return v___x_1333_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateProjS_x21(lean_object* v_m_1334_, lean_object* v_inst_1335_, lean_object* v_inst_1336_, lean_object* v_e_1337_, lean_object* v_newExpr_1338_){
_start:
{
if (lean_obj_tag(v_e_1337_) == 11)
{
lean_object* v_typeName_1339_; lean_object* v_idx_1340_; lean_object* v_struct_1341_; uint8_t v___x_1342_; 
v_typeName_1339_ = lean_ctor_get(v_e_1337_, 0);
v_idx_1340_ = lean_ctor_get(v_e_1337_, 1);
v_struct_1341_ = lean_ctor_get(v_e_1337_, 2);
v___x_1342_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_1341_, v_newExpr_1338_);
if (v___x_1342_ == 0)
{
lean_object* v___x_1343_; 
lean_inc(v_idx_1340_);
lean_inc(v_typeName_1339_);
lean_dec_ref_known(v_e_1337_, 3);
v___x_1343_ = l_Lean_Meta_Sym_Internal_mkProjS___redArg(v_inst_1335_, v_inst_1336_, v_typeName_1339_, v_idx_1340_, v_newExpr_1338_);
return v___x_1343_;
}
else
{
lean_object* v_toApplicative_1344_; lean_object* v_toPure_1345_; lean_object* v___x_1346_; 
lean_dec_ref(v_newExpr_1338_);
lean_dec_ref(v_inst_1335_);
v_toApplicative_1344_ = lean_ctor_get(v_inst_1336_, 0);
lean_inc_ref(v_toApplicative_1344_);
lean_dec_ref(v_inst_1336_);
v_toPure_1345_ = lean_ctor_get(v_toApplicative_1344_, 1);
lean_inc(v_toPure_1345_);
lean_dec_ref(v_toApplicative_1344_);
v___x_1346_ = lean_apply_2(v_toPure_1345_, lean_box(0), v_e_1337_);
return v___x_1346_;
}
}
else
{
lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; 
lean_dec_ref(v_newExpr_1338_);
lean_dec_ref(v_e_1337_);
lean_dec_ref(v_inst_1335_);
v___x_1347_ = l_Lean_instInhabitedExpr;
v___x_1348_ = l_instInhabitedOfMonad___redArg(v_inst_1336_, v___x_1347_);
v___x_1349_ = lean_obj_once(&l_Lean_Expr_updateProjS_x21___redArg___closed__2, &l_Lean_Expr_updateProjS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateProjS_x21___redArg___closed__2);
v___x_1350_ = l_panic___redArg(v___x_1348_, v___x_1349_);
lean_dec(v___x_1348_);
return v___x_1350_;
}
}
}
static lean_object* _init_l_Lean_Expr_updateForallS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; 
v___x_1353_ = ((lean_object*)(l_Lean_Expr_updateForallS_x21___redArg___closed__1));
v___x_1354_ = lean_unsigned_to_nat(31u);
v___x_1355_ = lean_unsigned_to_nat(160u);
v___x_1356_ = ((lean_object*)(l_Lean_Expr_updateForallS_x21___redArg___closed__0));
v___x_1357_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1358_ = l_mkPanicMessageWithDecl(v___x_1357_, v___x_1356_, v___x_1355_, v___x_1354_, v___x_1353_);
return v___x_1358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallS_x21___redArg(lean_object* v_inst_1359_, lean_object* v_inst_1360_, lean_object* v_e_1361_, lean_object* v_newDomain_1362_, lean_object* v_newBody_1363_){
_start:
{
if (lean_obj_tag(v_e_1361_) == 7)
{
lean_object* v_binderName_1364_; lean_object* v_binderType_1365_; lean_object* v_body_1366_; uint8_t v_binderInfo_1367_; uint8_t v___y_1369_; uint8_t v___x_1374_; 
v_binderName_1364_ = lean_ctor_get(v_e_1361_, 0);
v_binderType_1365_ = lean_ctor_get(v_e_1361_, 1);
v_body_1366_ = lean_ctor_get(v_e_1361_, 2);
v_binderInfo_1367_ = lean_ctor_get_uint8(v_e_1361_, sizeof(void*)*3 + 8);
v___x_1374_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_1365_, v_newDomain_1362_);
if (v___x_1374_ == 0)
{
v___y_1369_ = v___x_1374_;
goto v___jp_1368_;
}
else
{
uint8_t v___x_1375_; 
v___x_1375_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1366_, v_newBody_1363_);
v___y_1369_ = v___x_1375_;
goto v___jp_1368_;
}
v___jp_1368_:
{
if (v___y_1369_ == 0)
{
lean_object* v___x_1370_; 
lean_inc(v_binderName_1364_);
lean_dec_ref_known(v_e_1361_, 3);
v___x_1370_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v_inst_1359_, v_inst_1360_, v_binderName_1364_, v_binderInfo_1367_, v_newDomain_1362_, v_newBody_1363_);
return v___x_1370_;
}
else
{
lean_object* v_toApplicative_1371_; lean_object* v_toPure_1372_; lean_object* v___x_1373_; 
lean_dec_ref(v_newBody_1363_);
lean_dec_ref(v_newDomain_1362_);
lean_dec_ref(v_inst_1359_);
v_toApplicative_1371_ = lean_ctor_get(v_inst_1360_, 0);
lean_inc_ref(v_toApplicative_1371_);
lean_dec_ref(v_inst_1360_);
v_toPure_1372_ = lean_ctor_get(v_toApplicative_1371_, 1);
lean_inc(v_toPure_1372_);
lean_dec_ref(v_toApplicative_1371_);
v___x_1373_ = lean_apply_2(v_toPure_1372_, lean_box(0), v_e_1361_);
return v___x_1373_;
}
}
}
else
{
lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; 
lean_dec_ref(v_newBody_1363_);
lean_dec_ref(v_newDomain_1362_);
lean_dec_ref(v_e_1361_);
lean_dec_ref(v_inst_1359_);
v___x_1376_ = l_Lean_instInhabitedExpr;
v___x_1377_ = l_instInhabitedOfMonad___redArg(v_inst_1360_, v___x_1376_);
v___x_1378_ = lean_obj_once(&l_Lean_Expr_updateForallS_x21___redArg___closed__2, &l_Lean_Expr_updateForallS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateForallS_x21___redArg___closed__2);
v___x_1379_ = l_panic___redArg(v___x_1377_, v___x_1378_);
lean_dec(v___x_1377_);
return v___x_1379_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallS_x21(lean_object* v_m_1380_, lean_object* v_inst_1381_, lean_object* v_inst_1382_, lean_object* v_e_1383_, lean_object* v_newDomain_1384_, lean_object* v_newBody_1385_){
_start:
{
if (lean_obj_tag(v_e_1383_) == 7)
{
lean_object* v_binderName_1386_; lean_object* v_binderType_1387_; lean_object* v_body_1388_; uint8_t v_binderInfo_1389_; uint8_t v___y_1391_; uint8_t v___x_1396_; 
v_binderName_1386_ = lean_ctor_get(v_e_1383_, 0);
v_binderType_1387_ = lean_ctor_get(v_e_1383_, 1);
v_body_1388_ = lean_ctor_get(v_e_1383_, 2);
v_binderInfo_1389_ = lean_ctor_get_uint8(v_e_1383_, sizeof(void*)*3 + 8);
v___x_1396_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_1387_, v_newDomain_1384_);
if (v___x_1396_ == 0)
{
v___y_1391_ = v___x_1396_;
goto v___jp_1390_;
}
else
{
uint8_t v___x_1397_; 
v___x_1397_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1388_, v_newBody_1385_);
v___y_1391_ = v___x_1397_;
goto v___jp_1390_;
}
v___jp_1390_:
{
if (v___y_1391_ == 0)
{
lean_object* v___x_1392_; 
lean_inc(v_binderName_1386_);
lean_dec_ref_known(v_e_1383_, 3);
v___x_1392_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v_inst_1381_, v_inst_1382_, v_binderName_1386_, v_binderInfo_1389_, v_newDomain_1384_, v_newBody_1385_);
return v___x_1392_;
}
else
{
lean_object* v_toApplicative_1393_; lean_object* v_toPure_1394_; lean_object* v___x_1395_; 
lean_dec_ref(v_newBody_1385_);
lean_dec_ref(v_newDomain_1384_);
lean_dec_ref(v_inst_1381_);
v_toApplicative_1393_ = lean_ctor_get(v_inst_1382_, 0);
lean_inc_ref(v_toApplicative_1393_);
lean_dec_ref(v_inst_1382_);
v_toPure_1394_ = lean_ctor_get(v_toApplicative_1393_, 1);
lean_inc(v_toPure_1394_);
lean_dec_ref(v_toApplicative_1393_);
v___x_1395_ = lean_apply_2(v_toPure_1394_, lean_box(0), v_e_1383_);
return v___x_1395_;
}
}
}
else
{
lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; 
lean_dec_ref(v_newBody_1385_);
lean_dec_ref(v_newDomain_1384_);
lean_dec_ref(v_e_1383_);
lean_dec_ref(v_inst_1381_);
v___x_1398_ = l_Lean_instInhabitedExpr;
v___x_1399_ = l_instInhabitedOfMonad___redArg(v_inst_1382_, v___x_1398_);
v___x_1400_ = lean_obj_once(&l_Lean_Expr_updateForallS_x21___redArg___closed__2, &l_Lean_Expr_updateForallS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateForallS_x21___redArg___closed__2);
v___x_1401_ = l_panic___redArg(v___x_1399_, v___x_1400_);
lean_dec(v___x_1399_);
return v___x_1401_;
}
}
}
static lean_object* _init_l_Lean_Expr_updateLambdaS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; 
v___x_1404_ = ((lean_object*)(l_Lean_Expr_updateLambdaS_x21___redArg___closed__1));
v___x_1405_ = lean_unsigned_to_nat(27u);
v___x_1406_ = lean_unsigned_to_nat(167u);
v___x_1407_ = ((lean_object*)(l_Lean_Expr_updateLambdaS_x21___redArg___closed__0));
v___x_1408_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1409_ = l_mkPanicMessageWithDecl(v___x_1408_, v___x_1407_, v___x_1406_, v___x_1405_, v___x_1404_);
return v___x_1409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLambdaS_x21___redArg(lean_object* v_inst_1410_, lean_object* v_inst_1411_, lean_object* v_e_1412_, lean_object* v_newDomain_1413_, lean_object* v_newBody_1414_){
_start:
{
if (lean_obj_tag(v_e_1412_) == 6)
{
lean_object* v_binderName_1415_; lean_object* v_binderType_1416_; lean_object* v_body_1417_; uint8_t v_binderInfo_1418_; uint8_t v___y_1420_; uint8_t v___x_1425_; 
v_binderName_1415_ = lean_ctor_get(v_e_1412_, 0);
v_binderType_1416_ = lean_ctor_get(v_e_1412_, 1);
v_body_1417_ = lean_ctor_get(v_e_1412_, 2);
v_binderInfo_1418_ = lean_ctor_get_uint8(v_e_1412_, sizeof(void*)*3 + 8);
v___x_1425_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_1416_, v_newDomain_1413_);
if (v___x_1425_ == 0)
{
v___y_1420_ = v___x_1425_;
goto v___jp_1419_;
}
else
{
uint8_t v___x_1426_; 
v___x_1426_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1417_, v_newBody_1414_);
v___y_1420_ = v___x_1426_;
goto v___jp_1419_;
}
v___jp_1419_:
{
if (v___y_1420_ == 0)
{
lean_object* v___x_1421_; 
lean_inc(v_binderName_1415_);
lean_dec_ref_known(v_e_1412_, 3);
v___x_1421_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v_inst_1410_, v_inst_1411_, v_binderName_1415_, v_binderInfo_1418_, v_newDomain_1413_, v_newBody_1414_);
return v___x_1421_;
}
else
{
lean_object* v_toApplicative_1422_; lean_object* v_toPure_1423_; lean_object* v___x_1424_; 
lean_dec_ref(v_newBody_1414_);
lean_dec_ref(v_newDomain_1413_);
lean_dec_ref(v_inst_1410_);
v_toApplicative_1422_ = lean_ctor_get(v_inst_1411_, 0);
lean_inc_ref(v_toApplicative_1422_);
lean_dec_ref(v_inst_1411_);
v_toPure_1423_ = lean_ctor_get(v_toApplicative_1422_, 1);
lean_inc(v_toPure_1423_);
lean_dec_ref(v_toApplicative_1422_);
v___x_1424_ = lean_apply_2(v_toPure_1423_, lean_box(0), v_e_1412_);
return v___x_1424_;
}
}
}
else
{
lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; 
lean_dec_ref(v_newBody_1414_);
lean_dec_ref(v_newDomain_1413_);
lean_dec_ref(v_e_1412_);
lean_dec_ref(v_inst_1410_);
v___x_1427_ = l_Lean_instInhabitedExpr;
v___x_1428_ = l_instInhabitedOfMonad___redArg(v_inst_1411_, v___x_1427_);
v___x_1429_ = lean_obj_once(&l_Lean_Expr_updateLambdaS_x21___redArg___closed__2, &l_Lean_Expr_updateLambdaS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateLambdaS_x21___redArg___closed__2);
v___x_1430_ = l_panic___redArg(v___x_1428_, v___x_1429_);
lean_dec(v___x_1428_);
return v___x_1430_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLambdaS_x21(lean_object* v_m_1431_, lean_object* v_inst_1432_, lean_object* v_inst_1433_, lean_object* v_e_1434_, lean_object* v_newDomain_1435_, lean_object* v_newBody_1436_){
_start:
{
if (lean_obj_tag(v_e_1434_) == 6)
{
lean_object* v_binderName_1437_; lean_object* v_binderType_1438_; lean_object* v_body_1439_; uint8_t v_binderInfo_1440_; uint8_t v___y_1442_; uint8_t v___x_1447_; 
v_binderName_1437_ = lean_ctor_get(v_e_1434_, 0);
v_binderType_1438_ = lean_ctor_get(v_e_1434_, 1);
v_body_1439_ = lean_ctor_get(v_e_1434_, 2);
v_binderInfo_1440_ = lean_ctor_get_uint8(v_e_1434_, sizeof(void*)*3 + 8);
v___x_1447_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_1438_, v_newDomain_1435_);
if (v___x_1447_ == 0)
{
v___y_1442_ = v___x_1447_;
goto v___jp_1441_;
}
else
{
uint8_t v___x_1448_; 
v___x_1448_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1439_, v_newBody_1436_);
v___y_1442_ = v___x_1448_;
goto v___jp_1441_;
}
v___jp_1441_:
{
if (v___y_1442_ == 0)
{
lean_object* v___x_1443_; 
lean_inc(v_binderName_1437_);
lean_dec_ref_known(v_e_1434_, 3);
v___x_1443_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v_inst_1432_, v_inst_1433_, v_binderName_1437_, v_binderInfo_1440_, v_newDomain_1435_, v_newBody_1436_);
return v___x_1443_;
}
else
{
lean_object* v_toApplicative_1444_; lean_object* v_toPure_1445_; lean_object* v___x_1446_; 
lean_dec_ref(v_newBody_1436_);
lean_dec_ref(v_newDomain_1435_);
lean_dec_ref(v_inst_1432_);
v_toApplicative_1444_ = lean_ctor_get(v_inst_1433_, 0);
lean_inc_ref(v_toApplicative_1444_);
lean_dec_ref(v_inst_1433_);
v_toPure_1445_ = lean_ctor_get(v_toApplicative_1444_, 1);
lean_inc(v_toPure_1445_);
lean_dec_ref(v_toApplicative_1444_);
v___x_1446_ = lean_apply_2(v_toPure_1445_, lean_box(0), v_e_1434_);
return v___x_1446_;
}
}
}
else
{
lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; 
lean_dec_ref(v_newBody_1436_);
lean_dec_ref(v_newDomain_1435_);
lean_dec_ref(v_e_1434_);
lean_dec_ref(v_inst_1432_);
v___x_1449_ = l_Lean_instInhabitedExpr;
v___x_1450_ = l_instInhabitedOfMonad___redArg(v_inst_1433_, v___x_1449_);
v___x_1451_ = lean_obj_once(&l_Lean_Expr_updateLambdaS_x21___redArg___closed__2, &l_Lean_Expr_updateLambdaS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateLambdaS_x21___redArg___closed__2);
v___x_1452_ = l_panic___redArg(v___x_1450_, v___x_1451_);
lean_dec(v___x_1450_);
return v___x_1452_;
}
}
}
static lean_object* _init_l_Lean_Expr_updateLetS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; 
v___x_1455_ = ((lean_object*)(l_Lean_Expr_updateLetS_x21___redArg___closed__1));
v___x_1456_ = lean_unsigned_to_nat(34u);
v___x_1457_ = lean_unsigned_to_nat(174u);
v___x_1458_ = ((lean_object*)(l_Lean_Expr_updateLetS_x21___redArg___closed__0));
v___x_1459_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1460_ = l_mkPanicMessageWithDecl(v___x_1459_, v___x_1458_, v___x_1457_, v___x_1456_, v___x_1455_);
return v___x_1460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLetS_x21___redArg(lean_object* v_inst_1461_, lean_object* v_inst_1462_, lean_object* v_e_1463_, lean_object* v_newType_1464_, lean_object* v_newVal_1465_, lean_object* v_newBody_1466_){
_start:
{
if (lean_obj_tag(v_e_1463_) == 8)
{
lean_object* v_declName_1467_; lean_object* v_type_1468_; lean_object* v_value_1469_; lean_object* v_body_1470_; uint8_t v_nondep_1471_; uint8_t v___y_1473_; uint8_t v___x_1480_; 
v_declName_1467_ = lean_ctor_get(v_e_1463_, 0);
v_type_1468_ = lean_ctor_get(v_e_1463_, 1);
v_value_1469_ = lean_ctor_get(v_e_1463_, 2);
v_body_1470_ = lean_ctor_get(v_e_1463_, 3);
v_nondep_1471_ = lean_ctor_get_uint8(v_e_1463_, sizeof(void*)*4 + 8);
v___x_1480_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_type_1468_, v_newType_1464_);
if (v___x_1480_ == 0)
{
v___y_1473_ = v___x_1480_;
goto v___jp_1472_;
}
else
{
uint8_t v___x_1481_; 
v___x_1481_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_value_1469_, v_newVal_1465_);
v___y_1473_ = v___x_1481_;
goto v___jp_1472_;
}
v___jp_1472_:
{
if (v___y_1473_ == 0)
{
lean_object* v___x_1474_; 
lean_inc(v_declName_1467_);
lean_dec_ref_known(v_e_1463_, 4);
v___x_1474_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1461_, v_inst_1462_, v_declName_1467_, v_newType_1464_, v_newVal_1465_, v_newBody_1466_, v_nondep_1471_);
return v___x_1474_;
}
else
{
uint8_t v___x_1475_; 
v___x_1475_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1470_, v_newBody_1466_);
if (v___x_1475_ == 0)
{
lean_object* v___x_1476_; 
lean_inc(v_declName_1467_);
lean_dec_ref_known(v_e_1463_, 4);
v___x_1476_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1461_, v_inst_1462_, v_declName_1467_, v_newType_1464_, v_newVal_1465_, v_newBody_1466_, v_nondep_1471_);
return v___x_1476_;
}
else
{
lean_object* v_toApplicative_1477_; lean_object* v_toPure_1478_; lean_object* v___x_1479_; 
lean_dec_ref(v_newBody_1466_);
lean_dec_ref(v_newVal_1465_);
lean_dec_ref(v_newType_1464_);
lean_dec_ref(v_inst_1461_);
v_toApplicative_1477_ = lean_ctor_get(v_inst_1462_, 0);
lean_inc_ref(v_toApplicative_1477_);
lean_dec_ref(v_inst_1462_);
v_toPure_1478_ = lean_ctor_get(v_toApplicative_1477_, 1);
lean_inc(v_toPure_1478_);
lean_dec_ref(v_toApplicative_1477_);
v___x_1479_ = lean_apply_2(v_toPure_1478_, lean_box(0), v_e_1463_);
return v___x_1479_;
}
}
}
}
else
{
lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; 
lean_dec_ref(v_newBody_1466_);
lean_dec_ref(v_newVal_1465_);
lean_dec_ref(v_newType_1464_);
lean_dec_ref(v_e_1463_);
lean_dec_ref(v_inst_1461_);
v___x_1482_ = l_Lean_instInhabitedExpr;
v___x_1483_ = l_instInhabitedOfMonad___redArg(v_inst_1462_, v___x_1482_);
v___x_1484_ = lean_obj_once(&l_Lean_Expr_updateLetS_x21___redArg___closed__2, &l_Lean_Expr_updateLetS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateLetS_x21___redArg___closed__2);
v___x_1485_ = l_panic___redArg(v___x_1483_, v___x_1484_);
lean_dec(v___x_1483_);
return v___x_1485_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLetS_x21(lean_object* v_m_1486_, lean_object* v_inst_1487_, lean_object* v_inst_1488_, lean_object* v_e_1489_, lean_object* v_newType_1490_, lean_object* v_newVal_1491_, lean_object* v_newBody_1492_){
_start:
{
if (lean_obj_tag(v_e_1489_) == 8)
{
lean_object* v_declName_1493_; lean_object* v_type_1494_; lean_object* v_value_1495_; lean_object* v_body_1496_; uint8_t v_nondep_1497_; uint8_t v___y_1499_; uint8_t v___x_1506_; 
v_declName_1493_ = lean_ctor_get(v_e_1489_, 0);
v_type_1494_ = lean_ctor_get(v_e_1489_, 1);
v_value_1495_ = lean_ctor_get(v_e_1489_, 2);
v_body_1496_ = lean_ctor_get(v_e_1489_, 3);
v_nondep_1497_ = lean_ctor_get_uint8(v_e_1489_, sizeof(void*)*4 + 8);
v___x_1506_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_type_1494_, v_newType_1490_);
if (v___x_1506_ == 0)
{
v___y_1499_ = v___x_1506_;
goto v___jp_1498_;
}
else
{
uint8_t v___x_1507_; 
v___x_1507_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_value_1495_, v_newVal_1491_);
v___y_1499_ = v___x_1507_;
goto v___jp_1498_;
}
v___jp_1498_:
{
if (v___y_1499_ == 0)
{
lean_object* v___x_1500_; 
lean_inc(v_declName_1493_);
lean_dec_ref_known(v_e_1489_, 4);
v___x_1500_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1487_, v_inst_1488_, v_declName_1493_, v_newType_1490_, v_newVal_1491_, v_newBody_1492_, v_nondep_1497_);
return v___x_1500_;
}
else
{
uint8_t v___x_1501_; 
v___x_1501_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1496_, v_newBody_1492_);
if (v___x_1501_ == 0)
{
lean_object* v___x_1502_; 
lean_inc(v_declName_1493_);
lean_dec_ref_known(v_e_1489_, 4);
v___x_1502_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1487_, v_inst_1488_, v_declName_1493_, v_newType_1490_, v_newVal_1491_, v_newBody_1492_, v_nondep_1497_);
return v___x_1502_;
}
else
{
lean_object* v_toApplicative_1503_; lean_object* v_toPure_1504_; lean_object* v___x_1505_; 
lean_dec_ref(v_newBody_1492_);
lean_dec_ref(v_newVal_1491_);
lean_dec_ref(v_newType_1490_);
lean_dec_ref(v_inst_1487_);
v_toApplicative_1503_ = lean_ctor_get(v_inst_1488_, 0);
lean_inc_ref(v_toApplicative_1503_);
lean_dec_ref(v_inst_1488_);
v_toPure_1504_ = lean_ctor_get(v_toApplicative_1503_, 1);
lean_inc(v_toPure_1504_);
lean_dec_ref(v_toApplicative_1503_);
v___x_1505_ = lean_apply_2(v_toPure_1504_, lean_box(0), v_e_1489_);
return v___x_1505_;
}
}
}
}
else
{
lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; 
lean_dec_ref(v_newBody_1492_);
lean_dec_ref(v_newVal_1491_);
lean_dec_ref(v_newType_1490_);
lean_dec_ref(v_e_1489_);
lean_dec_ref(v_inst_1487_);
v___x_1508_ = l_Lean_instInhabitedExpr;
v___x_1509_ = l_instInhabitedOfMonad___redArg(v_inst_1488_, v___x_1508_);
v___x_1510_ = lean_obj_once(&l_Lean_Expr_updateLetS_x21___redArg___closed__2, &l_Lean_Expr_updateLetS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateLetS_x21___redArg___closed__2);
v___x_1511_ = l_panic___redArg(v___x_1509_, v___x_1510_);
lean_dec(v___x_1509_);
return v___x_1511_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___redArg___lam__0(lean_object* v_inst_1512_, lean_object* v_inst_1513_, lean_object* v_a_u2082_1514_, lean_object* v_____do__lift_1515_){
_start:
{
lean_object* v___x_1516_; 
v___x_1516_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1512_, v_inst_1513_, v_____do__lift_1515_, v_a_u2082_1514_);
return v___x_1516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___redArg(lean_object* v_inst_1517_, lean_object* v_inst_1518_, lean_object* v_f_1519_, lean_object* v_a_u2081_1520_, lean_object* v_a_u2082_1521_){
_start:
{
lean_object* v_toBind_1522_; lean_object* v___f_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; 
v_toBind_1522_ = lean_ctor_get(v_inst_1518_, 1);
lean_inc(v_toBind_1522_);
lean_inc_ref(v_inst_1518_);
lean_inc_ref(v_inst_1517_);
v___f_1523_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2082___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1523_, 0, v_inst_1517_);
lean_closure_set(v___f_1523_, 1, v_inst_1518_);
lean_closure_set(v___f_1523_, 2, v_a_u2082_1521_);
v___x_1524_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1517_, v_inst_1518_, v_f_1519_, v_a_u2081_1520_);
v___x_1525_ = lean_apply_4(v_toBind_1522_, lean_box(0), lean_box(0), v___x_1524_, v___f_1523_);
return v___x_1525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082(lean_object* v_m_1526_, lean_object* v_inst_1527_, lean_object* v_inst_1528_, lean_object* v_f_1529_, lean_object* v_a_u2081_1530_, lean_object* v_a_u2082_1531_){
_start:
{
lean_object* v___x_1532_; 
v___x_1532_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___redArg(v_inst_1527_, v_inst_1528_, v_f_1529_, v_a_u2081_1530_, v_a_u2082_1531_);
return v___x_1532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___redArg___lam__0(lean_object* v_inst_1533_, lean_object* v_inst_1534_, lean_object* v_a_u2083_1535_, lean_object* v_____do__lift_1536_){
_start:
{
lean_object* v___x_1537_; 
v___x_1537_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1533_, v_inst_1534_, v_____do__lift_1536_, v_a_u2083_1535_);
return v___x_1537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___redArg(lean_object* v_inst_1538_, lean_object* v_inst_1539_, lean_object* v_f_1540_, lean_object* v_a_u2081_1541_, lean_object* v_a_u2082_1542_, lean_object* v_a_u2083_1543_){
_start:
{
lean_object* v_toBind_1544_; lean_object* v___f_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; 
v_toBind_1544_ = lean_ctor_get(v_inst_1539_, 1);
lean_inc(v_toBind_1544_);
lean_inc_ref(v_inst_1539_);
lean_inc_ref(v_inst_1538_);
v___f_1545_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2083___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1545_, 0, v_inst_1538_);
lean_closure_set(v___f_1545_, 1, v_inst_1539_);
lean_closure_set(v___f_1545_, 2, v_a_u2083_1543_);
v___x_1546_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___redArg(v_inst_1538_, v_inst_1539_, v_f_1540_, v_a_u2081_1541_, v_a_u2082_1542_);
v___x_1547_ = lean_apply_4(v_toBind_1544_, lean_box(0), lean_box(0), v___x_1546_, v___f_1545_);
return v___x_1547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083(lean_object* v_m_1548_, lean_object* v_inst_1549_, lean_object* v_inst_1550_, lean_object* v_f_1551_, lean_object* v_a_u2081_1552_, lean_object* v_a_u2082_1553_, lean_object* v_a_u2083_1554_){
_start:
{
lean_object* v___x_1555_; 
v___x_1555_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___redArg(v_inst_1549_, v_inst_1550_, v_f_1551_, v_a_u2081_1552_, v_a_u2082_1553_, v_a_u2083_1554_);
return v___x_1555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___redArg___lam__0(lean_object* v_inst_1556_, lean_object* v_inst_1557_, lean_object* v_a_u2084_1558_, lean_object* v_____do__lift_1559_){
_start:
{
lean_object* v___x_1560_; 
v___x_1560_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1556_, v_inst_1557_, v_____do__lift_1559_, v_a_u2084_1558_);
return v___x_1560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___redArg(lean_object* v_inst_1561_, lean_object* v_inst_1562_, lean_object* v_f_1563_, lean_object* v_a_u2081_1564_, lean_object* v_a_u2082_1565_, lean_object* v_a_u2083_1566_, lean_object* v_a_u2084_1567_){
_start:
{
lean_object* v_toBind_1568_; lean_object* v___f_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; 
v_toBind_1568_ = lean_ctor_get(v_inst_1562_, 1);
lean_inc(v_toBind_1568_);
lean_inc_ref(v_inst_1562_);
lean_inc_ref(v_inst_1561_);
v___f_1569_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2084___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1569_, 0, v_inst_1561_);
lean_closure_set(v___f_1569_, 1, v_inst_1562_);
lean_closure_set(v___f_1569_, 2, v_a_u2084_1567_);
v___x_1570_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___redArg(v_inst_1561_, v_inst_1562_, v_f_1563_, v_a_u2081_1564_, v_a_u2082_1565_, v_a_u2083_1566_);
v___x_1571_ = lean_apply_4(v_toBind_1568_, lean_box(0), lean_box(0), v___x_1570_, v___f_1569_);
return v___x_1571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084(lean_object* v_m_1572_, lean_object* v_inst_1573_, lean_object* v_inst_1574_, lean_object* v_f_1575_, lean_object* v_a_u2081_1576_, lean_object* v_a_u2082_1577_, lean_object* v_a_u2083_1578_, lean_object* v_a_u2084_1579_){
_start:
{
lean_object* v___x_1580_; 
v___x_1580_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___redArg(v_inst_1573_, v_inst_1574_, v_f_1575_, v_a_u2081_1576_, v_a_u2082_1577_, v_a_u2083_1578_, v_a_u2084_1579_);
return v___x_1580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2085___redArg___lam__0(lean_object* v_inst_1581_, lean_object* v_inst_1582_, lean_object* v_a_u2085_1583_, lean_object* v_____do__lift_1584_){
_start:
{
lean_object* v___x_1585_; 
v___x_1585_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1581_, v_inst_1582_, v_____do__lift_1584_, v_a_u2085_1583_);
return v___x_1585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2085___redArg(lean_object* v_inst_1586_, lean_object* v_inst_1587_, lean_object* v_f_1588_, lean_object* v_a_u2081_1589_, lean_object* v_a_u2082_1590_, lean_object* v_a_u2083_1591_, lean_object* v_a_u2084_1592_, lean_object* v_a_u2085_1593_){
_start:
{
lean_object* v_toBind_1594_; lean_object* v___f_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; 
v_toBind_1594_ = lean_ctor_get(v_inst_1587_, 1);
lean_inc(v_toBind_1594_);
lean_inc_ref(v_inst_1587_);
lean_inc_ref(v_inst_1586_);
v___f_1595_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2085___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1595_, 0, v_inst_1586_);
lean_closure_set(v___f_1595_, 1, v_inst_1587_);
lean_closure_set(v___f_1595_, 2, v_a_u2085_1593_);
v___x_1596_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___redArg(v_inst_1586_, v_inst_1587_, v_f_1588_, v_a_u2081_1589_, v_a_u2082_1590_, v_a_u2083_1591_, v_a_u2084_1592_);
v___x_1597_ = lean_apply_4(v_toBind_1594_, lean_box(0), lean_box(0), v___x_1596_, v___f_1595_);
return v___x_1597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2085(lean_object* v_m_1598_, lean_object* v_inst_1599_, lean_object* v_inst_1600_, lean_object* v_f_1601_, lean_object* v_a_u2081_1602_, lean_object* v_a_u2082_1603_, lean_object* v_a_u2083_1604_, lean_object* v_a_u2084_1605_, lean_object* v_a_u2085_1606_){
_start:
{
lean_object* v___x_1607_; 
v___x_1607_ = l_Lean_Meta_Sym_Internal_mkAppS_u2085___redArg(v_inst_1599_, v_inst_1600_, v_f_1601_, v_a_u2081_1602_, v_a_u2082_1603_, v_a_u2083_1604_, v_a_u2084_1605_, v_a_u2085_1606_);
return v___x_1607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2086___redArg___lam__0(lean_object* v_inst_1608_, lean_object* v_inst_1609_, lean_object* v_a_u2086_1610_, lean_object* v_____do__lift_1611_){
_start:
{
lean_object* v___x_1612_; 
v___x_1612_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1608_, v_inst_1609_, v_____do__lift_1611_, v_a_u2086_1610_);
return v___x_1612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2086___redArg(lean_object* v_inst_1613_, lean_object* v_inst_1614_, lean_object* v_f_1615_, lean_object* v_a_u2081_1616_, lean_object* v_a_u2082_1617_, lean_object* v_a_u2083_1618_, lean_object* v_a_u2084_1619_, lean_object* v_a_u2085_1620_, lean_object* v_a_u2086_1621_){
_start:
{
lean_object* v_toBind_1622_; lean_object* v___f_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; 
v_toBind_1622_ = lean_ctor_get(v_inst_1614_, 1);
lean_inc(v_toBind_1622_);
lean_inc_ref(v_inst_1614_);
lean_inc_ref(v_inst_1613_);
v___f_1623_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2086___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1623_, 0, v_inst_1613_);
lean_closure_set(v___f_1623_, 1, v_inst_1614_);
lean_closure_set(v___f_1623_, 2, v_a_u2086_1621_);
v___x_1624_ = l_Lean_Meta_Sym_Internal_mkAppS_u2085___redArg(v_inst_1613_, v_inst_1614_, v_f_1615_, v_a_u2081_1616_, v_a_u2082_1617_, v_a_u2083_1618_, v_a_u2084_1619_, v_a_u2085_1620_);
v___x_1625_ = lean_apply_4(v_toBind_1622_, lean_box(0), lean_box(0), v___x_1624_, v___f_1623_);
return v___x_1625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2086(lean_object* v_m_1626_, lean_object* v_inst_1627_, lean_object* v_inst_1628_, lean_object* v_f_1629_, lean_object* v_a_u2081_1630_, lean_object* v_a_u2082_1631_, lean_object* v_a_u2083_1632_, lean_object* v_a_u2084_1633_, lean_object* v_a_u2085_1634_, lean_object* v_a_u2086_1635_){
_start:
{
lean_object* v___x_1636_; 
v___x_1636_ = l_Lean_Meta_Sym_Internal_mkAppS_u2086___redArg(v_inst_1627_, v_inst_1628_, v_f_1629_, v_a_u2081_1630_, v_a_u2082_1631_, v_a_u2083_1632_, v_a_u2084_1633_, v_a_u2085_1634_, v_a_u2086_1635_);
return v___x_1636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2087___redArg___lam__0(lean_object* v_inst_1637_, lean_object* v_inst_1638_, lean_object* v_a_u2087_1639_, lean_object* v_____do__lift_1640_){
_start:
{
lean_object* v___x_1641_; 
v___x_1641_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1637_, v_inst_1638_, v_____do__lift_1640_, v_a_u2087_1639_);
return v___x_1641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2087___redArg(lean_object* v_inst_1642_, lean_object* v_inst_1643_, lean_object* v_f_1644_, lean_object* v_a_u2081_1645_, lean_object* v_a_u2082_1646_, lean_object* v_a_u2083_1647_, lean_object* v_a_u2084_1648_, lean_object* v_a_u2085_1649_, lean_object* v_a_u2086_1650_, lean_object* v_a_u2087_1651_){
_start:
{
lean_object* v_toBind_1652_; lean_object* v___f_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; 
v_toBind_1652_ = lean_ctor_get(v_inst_1643_, 1);
lean_inc(v_toBind_1652_);
lean_inc_ref(v_inst_1643_);
lean_inc_ref(v_inst_1642_);
v___f_1653_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2087___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1653_, 0, v_inst_1642_);
lean_closure_set(v___f_1653_, 1, v_inst_1643_);
lean_closure_set(v___f_1653_, 2, v_a_u2087_1651_);
v___x_1654_ = l_Lean_Meta_Sym_Internal_mkAppS_u2086___redArg(v_inst_1642_, v_inst_1643_, v_f_1644_, v_a_u2081_1645_, v_a_u2082_1646_, v_a_u2083_1647_, v_a_u2084_1648_, v_a_u2085_1649_, v_a_u2086_1650_);
v___x_1655_ = lean_apply_4(v_toBind_1652_, lean_box(0), lean_box(0), v___x_1654_, v___f_1653_);
return v___x_1655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2087(lean_object* v_m_1656_, lean_object* v_inst_1657_, lean_object* v_inst_1658_, lean_object* v_f_1659_, lean_object* v_a_u2081_1660_, lean_object* v_a_u2082_1661_, lean_object* v_a_u2083_1662_, lean_object* v_a_u2084_1663_, lean_object* v_a_u2085_1664_, lean_object* v_a_u2086_1665_, lean_object* v_a_u2087_1666_){
_start:
{
lean_object* v___x_1667_; 
v___x_1667_ = l_Lean_Meta_Sym_Internal_mkAppS_u2087___redArg(v_inst_1657_, v_inst_1658_, v_f_1659_, v_a_u2081_1660_, v_a_u2082_1661_, v_a_u2083_1662_, v_a_u2084_1663_, v_a_u2085_1664_, v_a_u2086_1665_, v_a_u2087_1666_);
return v___x_1667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2088___redArg___lam__0(lean_object* v_inst_1668_, lean_object* v_inst_1669_, lean_object* v_a_u2088_1670_, lean_object* v_____do__lift_1671_){
_start:
{
lean_object* v___x_1672_; 
v___x_1672_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1668_, v_inst_1669_, v_____do__lift_1671_, v_a_u2088_1670_);
return v___x_1672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2088___redArg(lean_object* v_inst_1673_, lean_object* v_inst_1674_, lean_object* v_f_1675_, lean_object* v_a_u2081_1676_, lean_object* v_a_u2082_1677_, lean_object* v_a_u2083_1678_, lean_object* v_a_u2084_1679_, lean_object* v_a_u2085_1680_, lean_object* v_a_u2086_1681_, lean_object* v_a_u2087_1682_, lean_object* v_a_u2088_1683_){
_start:
{
lean_object* v_toBind_1684_; lean_object* v___f_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; 
v_toBind_1684_ = lean_ctor_get(v_inst_1674_, 1);
lean_inc(v_toBind_1684_);
lean_inc_ref(v_inst_1674_);
lean_inc_ref(v_inst_1673_);
v___f_1685_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2088___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1685_, 0, v_inst_1673_);
lean_closure_set(v___f_1685_, 1, v_inst_1674_);
lean_closure_set(v___f_1685_, 2, v_a_u2088_1683_);
v___x_1686_ = l_Lean_Meta_Sym_Internal_mkAppS_u2087___redArg(v_inst_1673_, v_inst_1674_, v_f_1675_, v_a_u2081_1676_, v_a_u2082_1677_, v_a_u2083_1678_, v_a_u2084_1679_, v_a_u2085_1680_, v_a_u2086_1681_, v_a_u2087_1682_);
v___x_1687_ = lean_apply_4(v_toBind_1684_, lean_box(0), lean_box(0), v___x_1686_, v___f_1685_);
return v___x_1687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2088(lean_object* v_m_1688_, lean_object* v_inst_1689_, lean_object* v_inst_1690_, lean_object* v_f_1691_, lean_object* v_a_u2081_1692_, lean_object* v_a_u2082_1693_, lean_object* v_a_u2083_1694_, lean_object* v_a_u2084_1695_, lean_object* v_a_u2085_1696_, lean_object* v_a_u2086_1697_, lean_object* v_a_u2087_1698_, lean_object* v_a_u2088_1699_){
_start:
{
lean_object* v___x_1700_; 
v___x_1700_ = l_Lean_Meta_Sym_Internal_mkAppS_u2088___redArg(v_inst_1689_, v_inst_1690_, v_f_1691_, v_a_u2081_1692_, v_a_u2082_1693_, v_a_u2083_1694_, v_a_u2084_1695_, v_a_u2085_1696_, v_a_u2086_1697_, v_a_u2087_1698_, v_a_u2088_1699_);
return v___x_1700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2089___redArg___lam__0(lean_object* v_inst_1701_, lean_object* v_inst_1702_, lean_object* v_a_u2089_1703_, lean_object* v_____do__lift_1704_){
_start:
{
lean_object* v___x_1705_; 
v___x_1705_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1701_, v_inst_1702_, v_____do__lift_1704_, v_a_u2089_1703_);
return v___x_1705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2089___redArg(lean_object* v_inst_1706_, lean_object* v_inst_1707_, lean_object* v_f_1708_, lean_object* v_a_u2081_1709_, lean_object* v_a_u2082_1710_, lean_object* v_a_u2083_1711_, lean_object* v_a_u2084_1712_, lean_object* v_a_u2085_1713_, lean_object* v_a_u2086_1714_, lean_object* v_a_u2087_1715_, lean_object* v_a_u2088_1716_, lean_object* v_a_u2089_1717_){
_start:
{
lean_object* v_toBind_1718_; lean_object* v___f_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; 
v_toBind_1718_ = lean_ctor_get(v_inst_1707_, 1);
lean_inc(v_toBind_1718_);
lean_inc_ref(v_inst_1707_);
lean_inc_ref(v_inst_1706_);
v___f_1719_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2089___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1719_, 0, v_inst_1706_);
lean_closure_set(v___f_1719_, 1, v_inst_1707_);
lean_closure_set(v___f_1719_, 2, v_a_u2089_1717_);
v___x_1720_ = l_Lean_Meta_Sym_Internal_mkAppS_u2088___redArg(v_inst_1706_, v_inst_1707_, v_f_1708_, v_a_u2081_1709_, v_a_u2082_1710_, v_a_u2083_1711_, v_a_u2084_1712_, v_a_u2085_1713_, v_a_u2086_1714_, v_a_u2087_1715_, v_a_u2088_1716_);
v___x_1721_ = lean_apply_4(v_toBind_1718_, lean_box(0), lean_box(0), v___x_1720_, v___f_1719_);
return v___x_1721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2089(lean_object* v_m_1722_, lean_object* v_inst_1723_, lean_object* v_inst_1724_, lean_object* v_f_1725_, lean_object* v_a_u2081_1726_, lean_object* v_a_u2082_1727_, lean_object* v_a_u2083_1728_, lean_object* v_a_u2084_1729_, lean_object* v_a_u2085_1730_, lean_object* v_a_u2086_1731_, lean_object* v_a_u2087_1732_, lean_object* v_a_u2088_1733_, lean_object* v_a_u2089_1734_){
_start:
{
lean_object* v___x_1735_; 
v___x_1735_ = l_Lean_Meta_Sym_Internal_mkAppS_u2089___redArg(v_inst_1723_, v_inst_1724_, v_f_1725_, v_a_u2081_1726_, v_a_u2082_1727_, v_a_u2083_1728_, v_a_u2084_1729_, v_a_u2085_1730_, v_a_u2086_1731_, v_a_u2087_1732_, v_a_u2088_1733_, v_a_u2089_1734_);
return v___x_1735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2080___redArg___lam__0(lean_object* v_inst_1736_, lean_object* v_inst_1737_, lean_object* v_a_u2081_u2080_1738_, lean_object* v_____do__lift_1739_){
_start:
{
lean_object* v___x_1740_; 
v___x_1740_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1736_, v_inst_1737_, v_____do__lift_1739_, v_a_u2081_u2080_1738_);
return v___x_1740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2080___redArg(lean_object* v_inst_1741_, lean_object* v_inst_1742_, lean_object* v_f_1743_, lean_object* v_a_u2081_1744_, lean_object* v_a_u2082_1745_, lean_object* v_a_u2083_1746_, lean_object* v_a_u2084_1747_, lean_object* v_a_u2085_1748_, lean_object* v_a_u2086_1749_, lean_object* v_a_u2087_1750_, lean_object* v_a_u2088_1751_, lean_object* v_a_u2089_1752_, lean_object* v_a_u2081_u2080_1753_){
_start:
{
lean_object* v_toBind_1754_; lean_object* v___f_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; 
v_toBind_1754_ = lean_ctor_get(v_inst_1742_, 1);
lean_inc(v_toBind_1754_);
lean_inc_ref(v_inst_1742_);
lean_inc_ref(v_inst_1741_);
v___f_1755_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2080___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1755_, 0, v_inst_1741_);
lean_closure_set(v___f_1755_, 1, v_inst_1742_);
lean_closure_set(v___f_1755_, 2, v_a_u2081_u2080_1753_);
v___x_1756_ = l_Lean_Meta_Sym_Internal_mkAppS_u2089___redArg(v_inst_1741_, v_inst_1742_, v_f_1743_, v_a_u2081_1744_, v_a_u2082_1745_, v_a_u2083_1746_, v_a_u2084_1747_, v_a_u2085_1748_, v_a_u2086_1749_, v_a_u2087_1750_, v_a_u2088_1751_, v_a_u2089_1752_);
v___x_1757_ = lean_apply_4(v_toBind_1754_, lean_box(0), lean_box(0), v___x_1756_, v___f_1755_);
return v___x_1757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2080(lean_object* v_m_1758_, lean_object* v_inst_1759_, lean_object* v_inst_1760_, lean_object* v_f_1761_, lean_object* v_a_u2081_1762_, lean_object* v_a_u2082_1763_, lean_object* v_a_u2083_1764_, lean_object* v_a_u2084_1765_, lean_object* v_a_u2085_1766_, lean_object* v_a_u2086_1767_, lean_object* v_a_u2087_1768_, lean_object* v_a_u2088_1769_, lean_object* v_a_u2089_1770_, lean_object* v_a_u2081_u2080_1771_){
_start:
{
lean_object* v___x_1772_; 
v___x_1772_ = l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2080___redArg(v_inst_1759_, v_inst_1760_, v_f_1761_, v_a_u2081_1762_, v_a_u2082_1763_, v_a_u2083_1764_, v_a_u2084_1765_, v_a_u2085_1766_, v_a_u2086_1767_, v_a_u2087_1768_, v_a_u2088_1769_, v_a_u2089_1770_, v_a_u2081_u2080_1771_);
return v___x_1772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2081___redArg___lam__0(lean_object* v_inst_1773_, lean_object* v_inst_1774_, lean_object* v_a_u2081_u2081_1775_, lean_object* v_____do__lift_1776_){
_start:
{
lean_object* v___x_1777_; 
v___x_1777_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1773_, v_inst_1774_, v_____do__lift_1776_, v_a_u2081_u2081_1775_);
return v___x_1777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2081___redArg(lean_object* v_inst_1778_, lean_object* v_inst_1779_, lean_object* v_f_1780_, lean_object* v_a_u2081_1781_, lean_object* v_a_u2082_1782_, lean_object* v_a_u2083_1783_, lean_object* v_a_u2084_1784_, lean_object* v_a_u2085_1785_, lean_object* v_a_u2086_1786_, lean_object* v_a_u2087_1787_, lean_object* v_a_u2088_1788_, lean_object* v_a_u2089_1789_, lean_object* v_a_u2081_u2080_1790_, lean_object* v_a_u2081_u2081_1791_){
_start:
{
lean_object* v_toBind_1792_; lean_object* v___f_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; 
v_toBind_1792_ = lean_ctor_get(v_inst_1779_, 1);
lean_inc(v_toBind_1792_);
lean_inc_ref(v_inst_1779_);
lean_inc_ref(v_inst_1778_);
v___f_1793_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2081___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1793_, 0, v_inst_1778_);
lean_closure_set(v___f_1793_, 1, v_inst_1779_);
lean_closure_set(v___f_1793_, 2, v_a_u2081_u2081_1791_);
v___x_1794_ = l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2080___redArg(v_inst_1778_, v_inst_1779_, v_f_1780_, v_a_u2081_1781_, v_a_u2082_1782_, v_a_u2083_1783_, v_a_u2084_1784_, v_a_u2085_1785_, v_a_u2086_1786_, v_a_u2087_1787_, v_a_u2088_1788_, v_a_u2089_1789_, v_a_u2081_u2080_1790_);
v___x_1795_ = lean_apply_4(v_toBind_1792_, lean_box(0), lean_box(0), v___x_1794_, v___f_1793_);
return v___x_1795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2081(lean_object* v_m_1796_, lean_object* v_inst_1797_, lean_object* v_inst_1798_, lean_object* v_f_1799_, lean_object* v_a_u2081_1800_, lean_object* v_a_u2082_1801_, lean_object* v_a_u2083_1802_, lean_object* v_a_u2084_1803_, lean_object* v_a_u2085_1804_, lean_object* v_a_u2086_1805_, lean_object* v_a_u2087_1806_, lean_object* v_a_u2088_1807_, lean_object* v_a_u2089_1808_, lean_object* v_a_u2081_u2080_1809_, lean_object* v_a_u2081_u2081_1810_){
_start:
{
lean_object* v___x_1811_; 
v___x_1811_ = l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2081___redArg(v_inst_1797_, v_inst_1798_, v_f_1799_, v_a_u2081_1800_, v_a_u2082_1801_, v_a_u2083_1802_, v_a_u2084_1803_, v_a_u2085_1804_, v_a_u2086_1805_, v_a_u2087_1806_, v_a_u2088_1807_, v_a_u2089_1808_, v_a_u2081_u2080_1809_, v_a_u2081_u2081_1810_);
return v___x_1811_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg___lam__0___boxed(lean_object* v_i_1812_, lean_object* v_inst_1813_, lean_object* v_inst_1814_, lean_object* v_args_1815_, lean_object* v_endIdx_1816_, lean_object* v_____do__lift_1817_){
_start:
{
lean_object* v_res_1818_; 
v_res_1818_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg___lam__0(v_i_1812_, v_inst_1813_, v_inst_1814_, v_args_1815_, v_endIdx_1816_, v_____do__lift_1817_);
lean_dec(v_i_1812_);
return v_res_1818_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg(lean_object* v_inst_1819_, lean_object* v_inst_1820_, lean_object* v_args_1821_, lean_object* v_endIdx_1822_, lean_object* v_b_1823_, lean_object* v_i_1824_){
_start:
{
uint8_t v___x_1825_; 
v___x_1825_ = lean_nat_dec_le(v_endIdx_1822_, v_i_1824_);
if (v___x_1825_ == 0)
{
lean_object* v_toBind_1826_; lean_object* v___f_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; 
v_toBind_1826_ = lean_ctor_get(v_inst_1820_, 1);
lean_inc(v_toBind_1826_);
lean_inc_ref(v_args_1821_);
lean_inc_ref(v_inst_1820_);
lean_inc_ref(v_inst_1819_);
lean_inc(v_i_1824_);
v___f_1827_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1827_, 0, v_i_1824_);
lean_closure_set(v___f_1827_, 1, v_inst_1819_);
lean_closure_set(v___f_1827_, 2, v_inst_1820_);
lean_closure_set(v___f_1827_, 3, v_args_1821_);
lean_closure_set(v___f_1827_, 4, v_endIdx_1822_);
v___x_1828_ = l_Lean_instInhabitedExpr;
v___x_1829_ = lean_array_get(v___x_1828_, v_args_1821_, v_i_1824_);
lean_dec(v_i_1824_);
lean_dec_ref(v_args_1821_);
v___x_1830_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1819_, v_inst_1820_, v_b_1823_, v___x_1829_);
v___x_1831_ = lean_apply_4(v_toBind_1826_, lean_box(0), lean_box(0), v___x_1830_, v___f_1827_);
return v___x_1831_;
}
else
{
lean_object* v_toApplicative_1832_; lean_object* v_toPure_1833_; lean_object* v___x_1834_; 
lean_dec(v_i_1824_);
lean_dec(v_endIdx_1822_);
lean_dec_ref(v_args_1821_);
lean_dec_ref(v_inst_1819_);
v_toApplicative_1832_ = lean_ctor_get(v_inst_1820_, 0);
lean_inc_ref(v_toApplicative_1832_);
lean_dec_ref(v_inst_1820_);
v_toPure_1833_ = lean_ctor_get(v_toApplicative_1832_, 1);
lean_inc(v_toPure_1833_);
lean_dec_ref(v_toApplicative_1832_);
v___x_1834_ = lean_apply_2(v_toPure_1833_, lean_box(0), v_b_1823_);
return v___x_1834_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg___lam__0(lean_object* v_i_1835_, lean_object* v_inst_1836_, lean_object* v_inst_1837_, lean_object* v_args_1838_, lean_object* v_endIdx_1839_, lean_object* v_____do__lift_1840_){
_start:
{
lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; 
v___x_1841_ = lean_unsigned_to_nat(1u);
v___x_1842_ = lean_nat_add(v_i_1835_, v___x_1841_);
v___x_1843_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg(v_inst_1836_, v_inst_1837_, v_args_1838_, v_endIdx_1839_, v_____do__lift_1840_, v___x_1842_);
return v___x_1843_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go(lean_object* v_m_1844_, lean_object* v_inst_1845_, lean_object* v_inst_1846_, lean_object* v_args_1847_, lean_object* v_endIdx_1848_, lean_object* v_b_1849_, lean_object* v_i_1850_){
_start:
{
lean_object* v___x_1851_; 
v___x_1851_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg(v_inst_1845_, v_inst_1846_, v_args_1847_, v_endIdx_1848_, v_b_1849_, v_i_1850_);
return v___x_1851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRangeS___redArg(lean_object* v_inst_1852_, lean_object* v_inst_1853_, lean_object* v_f_1854_, lean_object* v_beginIdx_1855_, lean_object* v_endIdx_1856_, lean_object* v_args_1857_){
_start:
{
lean_object* v___x_1858_; 
v___x_1858_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg(v_inst_1852_, v_inst_1853_, v_args_1857_, v_endIdx_1856_, v_f_1854_, v_beginIdx_1855_);
return v___x_1858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRangeS(lean_object* v_m_1859_, lean_object* v_inst_1860_, lean_object* v_inst_1861_, lean_object* v_f_1862_, lean_object* v_beginIdx_1863_, lean_object* v_endIdx_1864_, lean_object* v_args_1865_){
_start:
{
lean_object* v___x_1866_; 
v___x_1866_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg(v_inst_1860_, v_inst_1861_, v_args_1865_, v_endIdx_1864_, v_f_1862_, v_beginIdx_1863_);
return v___x_1866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___redArg(lean_object* v_inst_1867_, lean_object* v_inst_1868_, lean_object* v_f_1869_, lean_object* v_args_1870_){
_start:
{
lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; 
v___x_1871_ = lean_unsigned_to_nat(0u);
v___x_1872_ = lean_array_get_size(v_args_1870_);
v___x_1873_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg(v_inst_1867_, v_inst_1868_, v_args_1870_, v___x_1872_, v_f_1869_, v___x_1871_);
return v___x_1873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS(lean_object* v_m_1874_, lean_object* v_inst_1875_, lean_object* v_inst_1876_, lean_object* v_f_1877_, lean_object* v_args_1878_){
_start:
{
lean_object* v___x_1879_; 
v___x_1879_ = l_Lean_Meta_Sym_Internal_mkAppNS___redArg(v_inst_1875_, v_inst_1876_, v_f_1877_, v_args_1878_);
return v___x_1879_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg___lam__0___boxed(lean_object* v_inst_1880_, lean_object* v_inst_1881_, lean_object* v_revArgs_1882_, lean_object* v_start_1883_, lean_object* v_i_1884_, lean_object* v_____do__lift_1885_){
_start:
{
lean_object* v_res_1886_; 
v_res_1886_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg___lam__0(v_inst_1880_, v_inst_1881_, v_revArgs_1882_, v_start_1883_, v_i_1884_, v_____do__lift_1885_);
lean_dec(v_i_1884_);
return v_res_1886_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg(lean_object* v_inst_1887_, lean_object* v_inst_1888_, lean_object* v_revArgs_1889_, lean_object* v_start_1890_, lean_object* v_b_1891_, lean_object* v_i_1892_){
_start:
{
uint8_t v___x_1893_; 
v___x_1893_ = lean_nat_dec_le(v_i_1892_, v_start_1890_);
if (v___x_1893_ == 0)
{
lean_object* v_toBind_1894_; lean_object* v___x_1895_; lean_object* v_i_1896_; lean_object* v___f_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; 
v_toBind_1894_ = lean_ctor_get(v_inst_1888_, 1);
lean_inc(v_toBind_1894_);
v___x_1895_ = lean_unsigned_to_nat(1u);
v_i_1896_ = lean_nat_sub(v_i_1892_, v___x_1895_);
lean_inc(v_i_1896_);
lean_inc_ref(v_revArgs_1889_);
lean_inc_ref(v_inst_1888_);
lean_inc_ref(v_inst_1887_);
v___f_1897_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1897_, 0, v_inst_1887_);
lean_closure_set(v___f_1897_, 1, v_inst_1888_);
lean_closure_set(v___f_1897_, 2, v_revArgs_1889_);
lean_closure_set(v___f_1897_, 3, v_start_1890_);
lean_closure_set(v___f_1897_, 4, v_i_1896_);
v___x_1898_ = l_Lean_instInhabitedExpr;
v___x_1899_ = lean_array_get(v___x_1898_, v_revArgs_1889_, v_i_1896_);
lean_dec(v_i_1896_);
lean_dec_ref(v_revArgs_1889_);
v___x_1900_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1887_, v_inst_1888_, v_b_1891_, v___x_1899_);
v___x_1901_ = lean_apply_4(v_toBind_1894_, lean_box(0), lean_box(0), v___x_1900_, v___f_1897_);
return v___x_1901_;
}
else
{
lean_object* v_toApplicative_1902_; lean_object* v_toPure_1903_; lean_object* v___x_1904_; 
lean_dec(v_start_1890_);
lean_dec_ref(v_revArgs_1889_);
lean_dec_ref(v_inst_1887_);
v_toApplicative_1902_ = lean_ctor_get(v_inst_1888_, 0);
lean_inc_ref(v_toApplicative_1902_);
lean_dec_ref(v_inst_1888_);
v_toPure_1903_ = lean_ctor_get(v_toApplicative_1902_, 1);
lean_inc(v_toPure_1903_);
lean_dec_ref(v_toApplicative_1902_);
v___x_1904_ = lean_apply_2(v_toPure_1903_, lean_box(0), v_b_1891_);
return v___x_1904_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg___lam__0(lean_object* v_inst_1905_, lean_object* v_inst_1906_, lean_object* v_revArgs_1907_, lean_object* v_start_1908_, lean_object* v_i_1909_, lean_object* v_____do__lift_1910_){
_start:
{
lean_object* v___x_1911_; 
v___x_1911_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg(v_inst_1905_, v_inst_1906_, v_revArgs_1907_, v_start_1908_, v_____do__lift_1910_, v_i_1909_);
return v___x_1911_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg___boxed(lean_object* v_inst_1912_, lean_object* v_inst_1913_, lean_object* v_revArgs_1914_, lean_object* v_start_1915_, lean_object* v_b_1916_, lean_object* v_i_1917_){
_start:
{
lean_object* v_res_1918_; 
v_res_1918_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg(v_inst_1912_, v_inst_1913_, v_revArgs_1914_, v_start_1915_, v_b_1916_, v_i_1917_);
lean_dec(v_i_1917_);
return v_res_1918_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go(lean_object* v_m_1919_, lean_object* v_inst_1920_, lean_object* v_inst_1921_, lean_object* v_revArgs_1922_, lean_object* v_start_1923_, lean_object* v_b_1924_, lean_object* v_i_1925_){
_start:
{
lean_object* v___x_1926_; 
v___x_1926_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg(v_inst_1920_, v_inst_1921_, v_revArgs_1922_, v_start_1923_, v_b_1924_, v_i_1925_);
return v___x_1926_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___boxed(lean_object* v_m_1927_, lean_object* v_inst_1928_, lean_object* v_inst_1929_, lean_object* v_revArgs_1930_, lean_object* v_start_1931_, lean_object* v_b_1932_, lean_object* v_i_1933_){
_start:
{
lean_object* v_res_1934_; 
v_res_1934_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go(v_m_1927_, v_inst_1928_, v_inst_1929_, v_revArgs_1930_, v_start_1931_, v_b_1932_, v_i_1933_);
lean_dec(v_i_1933_);
return v_res_1934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevRangeS___redArg(lean_object* v_inst_1935_, lean_object* v_inst_1936_, lean_object* v_f_1937_, lean_object* v_beginIdx_1938_, lean_object* v_endIdx_1939_, lean_object* v_revArgs_1940_){
_start:
{
lean_object* v___x_1941_; 
v___x_1941_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg(v_inst_1935_, v_inst_1936_, v_revArgs_1940_, v_beginIdx_1938_, v_f_1937_, v_endIdx_1939_);
return v___x_1941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevRangeS___redArg___boxed(lean_object* v_inst_1942_, lean_object* v_inst_1943_, lean_object* v_f_1944_, lean_object* v_beginIdx_1945_, lean_object* v_endIdx_1946_, lean_object* v_revArgs_1947_){
_start:
{
lean_object* v_res_1948_; 
v_res_1948_ = l_Lean_Meta_Sym_Internal_mkAppRevRangeS___redArg(v_inst_1942_, v_inst_1943_, v_f_1944_, v_beginIdx_1945_, v_endIdx_1946_, v_revArgs_1947_);
lean_dec(v_endIdx_1946_);
return v_res_1948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevRangeS(lean_object* v_m_1949_, lean_object* v_inst_1950_, lean_object* v_inst_1951_, lean_object* v_f_1952_, lean_object* v_beginIdx_1953_, lean_object* v_endIdx_1954_, lean_object* v_revArgs_1955_){
_start:
{
lean_object* v___x_1956_; 
v___x_1956_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg(v_inst_1950_, v_inst_1951_, v_revArgs_1955_, v_beginIdx_1953_, v_f_1952_, v_endIdx_1954_);
return v___x_1956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevRangeS___boxed(lean_object* v_m_1957_, lean_object* v_inst_1958_, lean_object* v_inst_1959_, lean_object* v_f_1960_, lean_object* v_beginIdx_1961_, lean_object* v_endIdx_1962_, lean_object* v_revArgs_1963_){
_start:
{
lean_object* v_res_1964_; 
v_res_1964_ = l_Lean_Meta_Sym_Internal_mkAppRevRangeS(v_m_1957_, v_inst_1958_, v_inst_1959_, v_f_1960_, v_beginIdx_1961_, v_endIdx_1962_, v_revArgs_1963_);
lean_dec(v_endIdx_1962_);
return v_res_1964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevS___redArg(lean_object* v_inst_1965_, lean_object* v_inst_1966_, lean_object* v_f_1967_, lean_object* v_revArgs_1968_){
_start:
{
lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; 
v___x_1969_ = lean_unsigned_to_nat(0u);
v___x_1970_ = lean_array_get_size(v_revArgs_1968_);
v___x_1971_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg(v_inst_1965_, v_inst_1966_, v_revArgs_1968_, v___x_1969_, v_f_1967_, v___x_1970_);
return v___x_1971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevS(lean_object* v_m_1972_, lean_object* v_inst_1973_, lean_object* v_inst_1974_, lean_object* v_f_1975_, lean_object* v_revArgs_1976_){
_start:
{
lean_object* v___x_1977_; 
v___x_1977_ = l_Lean_Meta_Sym_Internal_mkAppRevS___redArg(v_inst_1973_, v_inst_1974_, v_f_1975_, v_revArgs_1976_);
return v___x_1977_;
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
