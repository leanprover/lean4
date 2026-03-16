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
uint64_t l_Lean_Meta_Sym_instHashableAlphaKey___private__1(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Sym_instBEqAlphaKey___private__1(lean_object*, lean_object*);
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
lean_object* l_instMonadEST(lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_lit___override(lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_isDebugEnabled___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_read(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__1 = (const lean_object*)&l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__2 = (const lean_object*)&l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__3 = (const lean_object*)&l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__4 = (const lean_object*)&l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__4_value;
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
v___x_67_ = l_Lean_Meta_Sym_instBEqAlphaKey___private__1(v_x_52_, v_k_x27_66_);
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
v___x_122_ = l_Lean_Meta_Sym_instBEqAlphaKey___private__1(v_x_95_, v_key_117_);
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
v___x_174_ = l_Lean_Meta_Sym_instHashableAlphaKey___private__1(v_k_172_);
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
size_t v_x_2160__boxed_197_; size_t v_x_2161__boxed_198_; lean_object* v_res_199_; 
v_x_2160__boxed_197_ = lean_unbox_usize(v_x_193_);
lean_dec(v_x_193_);
v_x_2161__boxed_198_ = lean_unbox_usize(v_x_194_);
lean_dec(v_x_194_);
v_res_199_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg(v_x_192_, v_x_2160__boxed_197_, v_x_2161__boxed_198_, v_x_195_, v_x_196_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1___redArg(lean_object* v_x_200_, lean_object* v_x_201_, lean_object* v_x_202_){
_start:
{
uint64_t v___x_203_; size_t v___x_204_; size_t v___x_205_; lean_object* v___x_206_; 
v___x_203_ = l_Lean_Meta_Sym_instHashableAlphaKey___private__1(v_x_201_);
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
v___x_214_ = l_Lean_Meta_Sym_instBEqAlphaKey___private__1(v_k_209_, v_k_x27_213_);
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
v___x_235_ = l_Lean_Meta_Sym_instBEqAlphaKey___private__1(v_x_225_, v_key_234_);
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
size_t v_x_2354__boxed_246_; lean_object* v_res_247_; 
v_x_2354__boxed_246_ = lean_unbox_usize(v_x_243_);
lean_dec(v_x_243_);
v_res_247_ = l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg(v_x_242_, v_x_2354__boxed_246_, v_x_244_, v_x_245_);
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
v___x_254_ = l_Lean_Meta_Sym_instHashableAlphaKey___private__1(v_e_248_);
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
lean_object* v___x_259_; lean_object* v_share_260_; lean_object* v_maxFVar_261_; lean_object* v_proofInstInfo_262_; lean_object* v_inferType_263_; lean_object* v_getLevel_264_; lean_object* v_congrInfo_265_; lean_object* v_defEqI_266_; uint8_t v_debug_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_278_; 
lean_dec_ref(v___x_256_);
v___x_259_ = lean_st_ref_take(v_a_249_);
v_share_260_ = lean_ctor_get(v___x_259_, 0);
v_maxFVar_261_ = lean_ctor_get(v___x_259_, 1);
v_proofInstInfo_262_ = lean_ctor_get(v___x_259_, 2);
v_inferType_263_ = lean_ctor_get(v___x_259_, 3);
v_getLevel_264_ = lean_ctor_get(v___x_259_, 4);
v_congrInfo_265_ = lean_ctor_get(v___x_259_, 5);
v_defEqI_266_ = lean_ctor_get(v___x_259_, 6);
v_debug_267_ = lean_ctor_get_uint8(v___x_259_, sizeof(void*)*7);
v_isSharedCheck_278_ = !lean_is_exclusive(v___x_259_);
if (v_isSharedCheck_278_ == 0)
{
v___x_269_ = v___x_259_;
v_isShared_270_ = v_isSharedCheck_278_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_defEqI_266_);
lean_inc(v_congrInfo_265_);
lean_inc(v_getLevel_264_);
lean_inc(v_inferType_263_);
lean_inc(v_proofInstInfo_262_);
lean_inc(v_maxFVar_261_);
lean_inc(v_share_260_);
lean_dec(v___x_259_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_278_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_274_; 
v___x_271_ = lean_box(0);
lean_inc_ref(v_e_248_);
v___x_272_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1___redArg(v_share_260_, v_e_248_, v___x_271_);
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 0, v___x_272_);
v___x_274_ = v___x_269_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v___x_272_);
lean_ctor_set(v_reuseFailAlloc_277_, 1, v_maxFVar_261_);
lean_ctor_set(v_reuseFailAlloc_277_, 2, v_proofInstInfo_262_);
lean_ctor_set(v_reuseFailAlloc_277_, 3, v_inferType_263_);
lean_ctor_set(v_reuseFailAlloc_277_, 4, v_getLevel_264_);
lean_ctor_set(v_reuseFailAlloc_277_, 5, v_congrInfo_265_);
lean_ctor_set(v_reuseFailAlloc_277_, 6, v_defEqI_266_);
lean_ctor_set_uint8(v_reuseFailAlloc_277_, sizeof(void*)*7, v_debug_267_);
v___x_274_ = v_reuseFailAlloc_277_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_275_ = lean_st_ref_set(v_a_249_, v___x_274_);
v___x_276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_276_, 0, v_e_248_);
return v___x_276_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg___boxed(lean_object* v_e_279_, lean_object* v_a_280_, lean_object* v_a_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v_e_279_, v_a_280_);
lean_dec(v_a_280_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Sym_share1(lean_object* v_e_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_){
_start:
{
lean_object* v___x_291_; 
v___x_291_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v_e_283_, v_a_285_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___boxed(lean_object* v_e_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Lean_Meta_Sym_Internal_Sym_share1(v_e_292_, v_a_293_, v_a_294_, v_a_295_, v_a_296_, v_a_297_, v_a_298_);
lean_dec(v_a_298_);
lean_dec_ref(v_a_297_);
lean_dec(v_a_296_);
lean_dec_ref(v_a_295_);
lean_dec(v_a_294_);
lean_dec_ref(v_a_293_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0(lean_object* v_00_u03b2_301_, lean_object* v_x_302_, size_t v_x_303_, lean_object* v_x_304_, lean_object* v_x_305_){
_start:
{
lean_object* v___x_306_; 
v___x_306_ = l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg(v_x_302_, v_x_303_, v_x_304_, v_x_305_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___boxed(lean_object* v_00_u03b2_307_, lean_object* v_x_308_, lean_object* v_x_309_, lean_object* v_x_310_, lean_object* v_x_311_){
_start:
{
size_t v_x_2465__boxed_312_; lean_object* v_res_313_; 
v_x_2465__boxed_312_ = lean_unbox_usize(v_x_309_);
lean_dec(v_x_309_);
v_res_313_ = l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0(v_00_u03b2_307_, v_x_308_, v_x_2465__boxed_312_, v_x_310_, v_x_311_);
lean_dec_ref(v_x_311_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1(lean_object* v_00_u03b2_314_, lean_object* v_x_315_, lean_object* v_x_316_, lean_object* v_x_317_){
_start:
{
lean_object* v___x_318_; 
v___x_318_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1___redArg(v_x_315_, v_x_316_, v_x_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0(lean_object* v_00_u03b2_319_, lean_object* v_keys_320_, lean_object* v_vals_321_, lean_object* v_heq_322_, lean_object* v_i_323_, lean_object* v_k_324_, lean_object* v_k_u2080_325_){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0___redArg(v_keys_320_, v_i_323_, v_k_324_, v_k_u2080_325_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0___boxed(lean_object* v_00_u03b2_327_, lean_object* v_keys_328_, lean_object* v_vals_329_, lean_object* v_heq_330_, lean_object* v_i_331_, lean_object* v_k_332_, lean_object* v_k_u2080_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0(v_00_u03b2_327_, v_keys_328_, v_vals_329_, v_heq_330_, v_i_331_, v_k_332_, v_k_u2080_333_);
lean_dec_ref(v_k_u2080_333_);
lean_dec_ref(v_vals_329_);
lean_dec_ref(v_keys_328_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2(lean_object* v_00_u03b2_335_, lean_object* v_x_336_, size_t v_x_337_, size_t v_x_338_, lean_object* v_x_339_, lean_object* v_x_340_){
_start:
{
lean_object* v___x_341_; 
v___x_341_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg(v_x_336_, v_x_337_, v_x_338_, v_x_339_, v_x_340_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_342_, lean_object* v_x_343_, lean_object* v_x_344_, lean_object* v_x_345_, lean_object* v_x_346_, lean_object* v_x_347_){
_start:
{
size_t v_x_2489__boxed_348_; size_t v_x_2490__boxed_349_; lean_object* v_res_350_; 
v_x_2489__boxed_348_ = lean_unbox_usize(v_x_344_);
lean_dec(v_x_344_);
v_x_2490__boxed_349_ = lean_unbox_usize(v_x_345_);
lean_dec(v_x_345_);
v_res_350_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2(v_00_u03b2_342_, v_x_343_, v_x_2489__boxed_348_, v_x_2490__boxed_349_, v_x_346_, v_x_347_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_351_, lean_object* v_n_352_, lean_object* v_k_353_, lean_object* v_v_354_){
_start:
{
lean_object* v___x_355_; 
v___x_355_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__3___redArg(v_n_352_, v_k_353_, v_v_354_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_356_, size_t v_depth_357_, lean_object* v_keys_358_, lean_object* v_vals_359_, lean_object* v_heq_360_, lean_object* v_i_361_, lean_object* v_entries_362_){
_start:
{
lean_object* v___x_363_; 
v___x_363_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4___redArg(v_depth_357_, v_keys_358_, v_vals_359_, v_i_361_, v_entries_362_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_364_, lean_object* v_depth_365_, lean_object* v_keys_366_, lean_object* v_vals_367_, lean_object* v_heq_368_, lean_object* v_i_369_, lean_object* v_entries_370_){
_start:
{
size_t v_depth_boxed_371_; lean_object* v_res_372_; 
v_depth_boxed_371_ = lean_unbox_usize(v_depth_365_);
lean_dec(v_depth_365_);
v_res_372_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4(v_00_u03b2_364_, v_depth_boxed_371_, v_keys_366_, v_vals_367_, v_heq_368_, v_i_369_, v_entries_370_);
lean_dec_ref(v_vals_367_);
lean_dec_ref(v_keys_366_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_373_, lean_object* v_x_374_, lean_object* v_x_375_, lean_object* v_x_376_, lean_object* v_x_377_){
_start:
{
lean_object* v___x_378_; 
v___x_378_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__3_spec__4___redArg(v_x_374_, v_x_375_, v_x_376_, v_x_377_);
return v___x_378_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0(void){
_start:
{
lean_object* v___x_379_; 
v___x_379_ = l_instMonadEST(lean_box(0), lean_box(0));
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0(lean_object* v_msg_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v_toApplicative_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_457_; 
v___x_392_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0, &l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0);
v___x_393_ = l_ReaderT_instMonad___redArg(v___x_392_);
v_toApplicative_394_ = lean_ctor_get(v___x_393_, 0);
v_isSharedCheck_457_ = !lean_is_exclusive(v___x_393_);
if (v_isSharedCheck_457_ == 0)
{
lean_object* v_unused_458_; 
v_unused_458_ = lean_ctor_get(v___x_393_, 1);
lean_dec(v_unused_458_);
v___x_396_ = v___x_393_;
v_isShared_397_ = v_isSharedCheck_457_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_toApplicative_394_);
lean_dec(v___x_393_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_457_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v_toFunctor_398_; lean_object* v_toSeq_399_; lean_object* v_toSeqLeft_400_; lean_object* v_toSeqRight_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_455_; 
v_toFunctor_398_ = lean_ctor_get(v_toApplicative_394_, 0);
v_toSeq_399_ = lean_ctor_get(v_toApplicative_394_, 2);
v_toSeqLeft_400_ = lean_ctor_get(v_toApplicative_394_, 3);
v_toSeqRight_401_ = lean_ctor_get(v_toApplicative_394_, 4);
v_isSharedCheck_455_ = !lean_is_exclusive(v_toApplicative_394_);
if (v_isSharedCheck_455_ == 0)
{
lean_object* v_unused_456_; 
v_unused_456_ = lean_ctor_get(v_toApplicative_394_, 1);
lean_dec(v_unused_456_);
v___x_403_ = v_toApplicative_394_;
v_isShared_404_ = v_isSharedCheck_455_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_toSeqRight_401_);
lean_inc(v_toSeqLeft_400_);
lean_inc(v_toSeq_399_);
lean_inc(v_toFunctor_398_);
lean_dec(v_toApplicative_394_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_455_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___f_405_; lean_object* v___f_406_; lean_object* v___f_407_; lean_object* v___f_408_; lean_object* v___x_409_; lean_object* v___f_410_; lean_object* v___f_411_; lean_object* v___f_412_; lean_object* v___x_414_; 
v___f_405_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__1));
v___f_406_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__2));
lean_inc_ref(v_toFunctor_398_);
v___f_407_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_407_, 0, v_toFunctor_398_);
v___f_408_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_408_, 0, v_toFunctor_398_);
v___x_409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_409_, 0, v___f_407_);
lean_ctor_set(v___x_409_, 1, v___f_408_);
v___f_410_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_410_, 0, v_toSeqRight_401_);
v___f_411_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_411_, 0, v_toSeqLeft_400_);
v___f_412_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_412_, 0, v_toSeq_399_);
if (v_isShared_404_ == 0)
{
lean_ctor_set(v___x_403_, 4, v___f_410_);
lean_ctor_set(v___x_403_, 3, v___f_411_);
lean_ctor_set(v___x_403_, 2, v___f_412_);
lean_ctor_set(v___x_403_, 1, v___f_405_);
lean_ctor_set(v___x_403_, 0, v___x_409_);
v___x_414_ = v___x_403_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v___x_409_);
lean_ctor_set(v_reuseFailAlloc_454_, 1, v___f_405_);
lean_ctor_set(v_reuseFailAlloc_454_, 2, v___f_412_);
lean_ctor_set(v_reuseFailAlloc_454_, 3, v___f_411_);
lean_ctor_set(v_reuseFailAlloc_454_, 4, v___f_410_);
v___x_414_ = v_reuseFailAlloc_454_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
lean_object* v___x_416_; 
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 1, v___f_406_);
lean_ctor_set(v___x_396_, 0, v___x_414_);
v___x_416_ = v___x_396_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v___x_414_);
lean_ctor_set(v_reuseFailAlloc_453_, 1, v___f_406_);
v___x_416_ = v_reuseFailAlloc_453_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
lean_object* v___x_417_; lean_object* v_toApplicative_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_451_; 
v___x_417_ = l_ReaderT_instMonad___redArg(v___x_416_);
v_toApplicative_418_ = lean_ctor_get(v___x_417_, 0);
v_isSharedCheck_451_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_451_ == 0)
{
lean_object* v_unused_452_; 
v_unused_452_ = lean_ctor_get(v___x_417_, 1);
lean_dec(v_unused_452_);
v___x_420_ = v___x_417_;
v_isShared_421_ = v_isSharedCheck_451_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_toApplicative_418_);
lean_dec(v___x_417_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_451_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v_toFunctor_422_; lean_object* v_toSeq_423_; lean_object* v_toSeqLeft_424_; lean_object* v_toSeqRight_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_449_; 
v_toFunctor_422_ = lean_ctor_get(v_toApplicative_418_, 0);
v_toSeq_423_ = lean_ctor_get(v_toApplicative_418_, 2);
v_toSeqLeft_424_ = lean_ctor_get(v_toApplicative_418_, 3);
v_toSeqRight_425_ = lean_ctor_get(v_toApplicative_418_, 4);
v_isSharedCheck_449_ = !lean_is_exclusive(v_toApplicative_418_);
if (v_isSharedCheck_449_ == 0)
{
lean_object* v_unused_450_; 
v_unused_450_ = lean_ctor_get(v_toApplicative_418_, 1);
lean_dec(v_unused_450_);
v___x_427_ = v_toApplicative_418_;
v_isShared_428_ = v_isSharedCheck_449_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_toSeqRight_425_);
lean_inc(v_toSeqLeft_424_);
lean_inc(v_toSeq_423_);
lean_inc(v_toFunctor_422_);
lean_dec(v_toApplicative_418_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_449_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v___f_429_; lean_object* v___f_430_; lean_object* v___f_431_; lean_object* v___f_432_; lean_object* v___x_433_; lean_object* v___f_434_; lean_object* v___f_435_; lean_object* v___f_436_; lean_object* v___x_438_; 
v___f_429_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__3));
v___f_430_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__4));
lean_inc_ref(v_toFunctor_422_);
v___f_431_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_431_, 0, v_toFunctor_422_);
v___f_432_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_432_, 0, v_toFunctor_422_);
v___x_433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_433_, 0, v___f_431_);
lean_ctor_set(v___x_433_, 1, v___f_432_);
v___f_434_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_434_, 0, v_toSeqRight_425_);
v___f_435_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_435_, 0, v_toSeqLeft_424_);
v___f_436_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_436_, 0, v_toSeq_423_);
if (v_isShared_428_ == 0)
{
lean_ctor_set(v___x_427_, 4, v___f_434_);
lean_ctor_set(v___x_427_, 3, v___f_435_);
lean_ctor_set(v___x_427_, 2, v___f_436_);
lean_ctor_set(v___x_427_, 1, v___f_429_);
lean_ctor_set(v___x_427_, 0, v___x_433_);
v___x_438_ = v___x_427_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v___x_433_);
lean_ctor_set(v_reuseFailAlloc_448_, 1, v___f_429_);
lean_ctor_set(v_reuseFailAlloc_448_, 2, v___f_436_);
lean_ctor_set(v_reuseFailAlloc_448_, 3, v___f_435_);
lean_ctor_set(v_reuseFailAlloc_448_, 4, v___f_434_);
v___x_438_ = v_reuseFailAlloc_448_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
lean_object* v___x_440_; 
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 1, v___f_430_);
lean_ctor_set(v___x_420_, 0, v___x_438_);
v___x_440_ = v___x_420_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v___x_438_);
lean_ctor_set(v_reuseFailAlloc_447_, 1, v___f_430_);
v___x_440_ = v_reuseFailAlloc_447_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___f_444_; lean_object* v___x_807__overap_445_; lean_object* v___x_446_; 
v___x_441_ = l_ReaderT_instMonad___redArg(v___x_440_);
v___x_442_ = lean_box(0);
v___x_443_ = l_instInhabitedOfMonad___redArg(v___x_441_, v___x_442_);
v___f_444_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_444_, 0, v___x_443_);
v___x_807__overap_445_ = lean_panic_fn(v___f_444_, v_msg_384_);
v___x_446_ = lean_apply_7(v___x_807__overap_445_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, lean_box(0));
return v___x_446_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___boxed(lean_object* v_msg_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0(v_msg_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_);
return v_res_467_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__3(void){
_start:
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_471_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__2));
v___x_472_ = lean_unsigned_to_nat(2u);
v___x_473_ = lean_unsigned_to_nat(42u);
v___x_474_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__1));
v___x_475_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_476_ = l_mkPanicMessageWithDecl(v___x_475_, v___x_474_, v___x_473_, v___x_472_, v___x_471_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object* v_e_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_){
_start:
{
lean_object* v___x_485_; lean_object* v_share_486_; lean_object* v___x_487_; uint64_t v___x_488_; size_t v___x_489_; lean_object* v___x_490_; uint8_t v___x_491_; 
v___x_485_ = lean_st_ref_get(v_a_479_);
v_share_486_ = lean_ctor_get(v___x_485_, 0);
lean_inc_ref(v_share_486_);
lean_dec(v___x_485_);
v___x_487_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy;
v___x_488_ = l_Lean_Meta_Sym_instHashableAlphaKey___private__1(v_e_477_);
v___x_489_ = lean_uint64_to_usize(v___x_488_);
lean_inc_ref(v_e_477_);
v___x_490_ = l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg(v_share_486_, v___x_489_, v_e_477_, v___x_487_);
v___x_491_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_490_, v_e_477_);
lean_dec_ref(v_e_477_);
lean_dec_ref(v___x_490_);
if (v___x_491_ == 0)
{
lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_492_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__3, &l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__3_once, _init_l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__3);
v___x_493_ = l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0(v___x_492_, v_a_478_, v_a_479_, v_a_480_, v_a_481_, v_a_482_, v_a_483_);
return v___x_493_;
}
else
{
lean_object* v___x_494_; lean_object* v___x_495_; 
lean_dec(v_a_483_);
lean_dec_ref(v_a_482_);
lean_dec(v_a_481_);
lean_dec_ref(v_a_480_);
lean_dec(v_a_479_);
lean_dec_ref(v_a_478_);
v___x_494_ = lean_box(0);
v___x_495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_495_, 0, v___x_494_);
return v___x_495_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared___boxed(lean_object* v_e_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_e_496_, v_a_497_, v_a_498_, v_a_499_, v_a_500_, v_a_501_, v_a_502_);
return v_res_504_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2(void){
_start:
{
lean_object* v___f_515_; lean_object* v___f_516_; lean_object* v___x_517_; 
v___f_515_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__1));
v___f_516_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__0));
v___x_517_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___f_516_, v___f_515_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM___redArg(lean_object* v_k_518_, lean_object* v_a_519_){
_start:
{
lean_object* v___x_521_; lean_object* v_share_522_; lean_object* v_maxFVar_523_; lean_object* v_proofInstInfo_524_; lean_object* v_inferType_525_; lean_object* v_getLevel_526_; lean_object* v_congrInfo_527_; lean_object* v_defEqI_528_; uint8_t v_debug_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_562_; 
v___x_521_ = lean_st_ref_take(v_a_519_);
v_share_522_ = lean_ctor_get(v___x_521_, 0);
v_maxFVar_523_ = lean_ctor_get(v___x_521_, 1);
v_proofInstInfo_524_ = lean_ctor_get(v___x_521_, 2);
v_inferType_525_ = lean_ctor_get(v___x_521_, 3);
v_getLevel_526_ = lean_ctor_get(v___x_521_, 4);
v_congrInfo_527_ = lean_ctor_get(v___x_521_, 5);
v_defEqI_528_ = lean_ctor_get(v___x_521_, 6);
v_debug_529_ = lean_ctor_get_uint8(v___x_521_, sizeof(void*)*7);
v_isSharedCheck_562_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_562_ == 0)
{
v___x_531_ = v___x_521_;
v_isShared_532_ = v_isSharedCheck_562_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_defEqI_528_);
lean_inc(v_congrInfo_527_);
lean_inc(v_getLevel_526_);
lean_inc(v_inferType_525_);
lean_inc(v_proofInstInfo_524_);
lean_inc(v_maxFVar_523_);
lean_inc(v_share_522_);
lean_dec(v___x_521_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_562_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v___x_533_; lean_object* v___x_535_; 
v___x_533_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2, &l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2_once, _init_l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2);
if (v_isShared_532_ == 0)
{
lean_ctor_set(v___x_531_, 0, v___x_533_);
v___x_535_ = v___x_531_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v___x_533_);
lean_ctor_set(v_reuseFailAlloc_561_, 1, v_maxFVar_523_);
lean_ctor_set(v_reuseFailAlloc_561_, 2, v_proofInstInfo_524_);
lean_ctor_set(v_reuseFailAlloc_561_, 3, v_inferType_525_);
lean_ctor_set(v_reuseFailAlloc_561_, 4, v_getLevel_526_);
lean_ctor_set(v_reuseFailAlloc_561_, 5, v_congrInfo_527_);
lean_ctor_set(v_reuseFailAlloc_561_, 6, v_defEqI_528_);
lean_ctor_set_uint8(v_reuseFailAlloc_561_, sizeof(void*)*7, v_debug_529_);
v___x_535_ = v_reuseFailAlloc_561_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
lean_object* v___x_536_; lean_object* v___x_537_; uint8_t v_debug_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v_fst_541_; lean_object* v_snd_542_; lean_object* v___x_543_; lean_object* v_maxFVar_544_; lean_object* v_proofInstInfo_545_; lean_object* v_inferType_546_; lean_object* v_getLevel_547_; lean_object* v_congrInfo_548_; lean_object* v_defEqI_549_; uint8_t v_debug_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_559_; 
v___x_536_ = lean_st_ref_set(v_a_519_, v___x_535_);
v___x_537_ = lean_st_ref_get(v_a_519_);
v_debug_538_ = lean_ctor_get_uint8(v___x_537_, sizeof(void*)*7);
lean_dec(v___x_537_);
v___x_539_ = lean_box(v_debug_538_);
v___x_540_ = lean_apply_2(v_k_518_, v___x_539_, v_share_522_);
v_fst_541_ = lean_ctor_get(v___x_540_, 0);
lean_inc(v_fst_541_);
v_snd_542_ = lean_ctor_get(v___x_540_, 1);
lean_inc(v_snd_542_);
lean_dec_ref(v___x_540_);
v___x_543_ = lean_st_ref_take(v_a_519_);
v_maxFVar_544_ = lean_ctor_get(v___x_543_, 1);
v_proofInstInfo_545_ = lean_ctor_get(v___x_543_, 2);
v_inferType_546_ = lean_ctor_get(v___x_543_, 3);
v_getLevel_547_ = lean_ctor_get(v___x_543_, 4);
v_congrInfo_548_ = lean_ctor_get(v___x_543_, 5);
v_defEqI_549_ = lean_ctor_get(v___x_543_, 6);
v_debug_550_ = lean_ctor_get_uint8(v___x_543_, sizeof(void*)*7);
v_isSharedCheck_559_ = !lean_is_exclusive(v___x_543_);
if (v_isSharedCheck_559_ == 0)
{
lean_object* v_unused_560_; 
v_unused_560_ = lean_ctor_get(v___x_543_, 0);
lean_dec(v_unused_560_);
v___x_552_ = v___x_543_;
v_isShared_553_ = v_isSharedCheck_559_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_defEqI_549_);
lean_inc(v_congrInfo_548_);
lean_inc(v_getLevel_547_);
lean_inc(v_inferType_546_);
lean_inc(v_proofInstInfo_545_);
lean_inc(v_maxFVar_544_);
lean_dec(v___x_543_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_559_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_555_; 
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 0, v_snd_542_);
v___x_555_ = v___x_552_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v_snd_542_);
lean_ctor_set(v_reuseFailAlloc_558_, 1, v_maxFVar_544_);
lean_ctor_set(v_reuseFailAlloc_558_, 2, v_proofInstInfo_545_);
lean_ctor_set(v_reuseFailAlloc_558_, 3, v_inferType_546_);
lean_ctor_set(v_reuseFailAlloc_558_, 4, v_getLevel_547_);
lean_ctor_set(v_reuseFailAlloc_558_, 5, v_congrInfo_548_);
lean_ctor_set(v_reuseFailAlloc_558_, 6, v_defEqI_549_);
lean_ctor_set_uint8(v_reuseFailAlloc_558_, sizeof(void*)*7, v_debug_550_);
v___x_555_ = v_reuseFailAlloc_558_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_556_ = lean_st_ref_set(v_a_519_, v___x_555_);
v___x_557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_557_, 0, v_fst_541_);
return v___x_557_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___boxed(lean_object* v_k_563_, lean_object* v_a_564_, lean_object* v_a_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l_Lean_Meta_Sym_Internal_liftBuilderM___redArg(v_k_563_, v_a_564_);
lean_dec(v_a_564_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM(lean_object* v_00_u03b1_567_, lean_object* v_k_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_){
_start:
{
lean_object* v___x_576_; lean_object* v_share_577_; lean_object* v_maxFVar_578_; lean_object* v_proofInstInfo_579_; lean_object* v_inferType_580_; lean_object* v_getLevel_581_; lean_object* v_congrInfo_582_; lean_object* v_defEqI_583_; uint8_t v_debug_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_617_; 
v___x_576_ = lean_st_ref_take(v_a_570_);
v_share_577_ = lean_ctor_get(v___x_576_, 0);
v_maxFVar_578_ = lean_ctor_get(v___x_576_, 1);
v_proofInstInfo_579_ = lean_ctor_get(v___x_576_, 2);
v_inferType_580_ = lean_ctor_get(v___x_576_, 3);
v_getLevel_581_ = lean_ctor_get(v___x_576_, 4);
v_congrInfo_582_ = lean_ctor_get(v___x_576_, 5);
v_defEqI_583_ = lean_ctor_get(v___x_576_, 6);
v_debug_584_ = lean_ctor_get_uint8(v___x_576_, sizeof(void*)*7);
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_576_);
if (v_isSharedCheck_617_ == 0)
{
v___x_586_ = v___x_576_;
v_isShared_587_ = v_isSharedCheck_617_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_defEqI_583_);
lean_inc(v_congrInfo_582_);
lean_inc(v_getLevel_581_);
lean_inc(v_inferType_580_);
lean_inc(v_proofInstInfo_579_);
lean_inc(v_maxFVar_578_);
lean_inc(v_share_577_);
lean_dec(v___x_576_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_617_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_588_; lean_object* v___x_590_; 
v___x_588_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2, &l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2_once, _init_l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2);
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 0, v___x_588_);
v___x_590_ = v___x_586_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v___x_588_);
lean_ctor_set(v_reuseFailAlloc_616_, 1, v_maxFVar_578_);
lean_ctor_set(v_reuseFailAlloc_616_, 2, v_proofInstInfo_579_);
lean_ctor_set(v_reuseFailAlloc_616_, 3, v_inferType_580_);
lean_ctor_set(v_reuseFailAlloc_616_, 4, v_getLevel_581_);
lean_ctor_set(v_reuseFailAlloc_616_, 5, v_congrInfo_582_);
lean_ctor_set(v_reuseFailAlloc_616_, 6, v_defEqI_583_);
lean_ctor_set_uint8(v_reuseFailAlloc_616_, sizeof(void*)*7, v_debug_584_);
v___x_590_ = v_reuseFailAlloc_616_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
lean_object* v___x_591_; lean_object* v___x_592_; uint8_t v_debug_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v_fst_596_; lean_object* v_snd_597_; lean_object* v___x_598_; lean_object* v_maxFVar_599_; lean_object* v_proofInstInfo_600_; lean_object* v_inferType_601_; lean_object* v_getLevel_602_; lean_object* v_congrInfo_603_; lean_object* v_defEqI_604_; uint8_t v_debug_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_614_; 
v___x_591_ = lean_st_ref_set(v_a_570_, v___x_590_);
v___x_592_ = lean_st_ref_get(v_a_570_);
v_debug_593_ = lean_ctor_get_uint8(v___x_592_, sizeof(void*)*7);
lean_dec(v___x_592_);
v___x_594_ = lean_box(v_debug_593_);
v___x_595_ = lean_apply_2(v_k_568_, v___x_594_, v_share_577_);
v_fst_596_ = lean_ctor_get(v___x_595_, 0);
lean_inc(v_fst_596_);
v_snd_597_ = lean_ctor_get(v___x_595_, 1);
lean_inc(v_snd_597_);
lean_dec_ref(v___x_595_);
v___x_598_ = lean_st_ref_take(v_a_570_);
v_maxFVar_599_ = lean_ctor_get(v___x_598_, 1);
v_proofInstInfo_600_ = lean_ctor_get(v___x_598_, 2);
v_inferType_601_ = lean_ctor_get(v___x_598_, 3);
v_getLevel_602_ = lean_ctor_get(v___x_598_, 4);
v_congrInfo_603_ = lean_ctor_get(v___x_598_, 5);
v_defEqI_604_ = lean_ctor_get(v___x_598_, 6);
v_debug_605_ = lean_ctor_get_uint8(v___x_598_, sizeof(void*)*7);
v_isSharedCheck_614_ = !lean_is_exclusive(v___x_598_);
if (v_isSharedCheck_614_ == 0)
{
lean_object* v_unused_615_; 
v_unused_615_ = lean_ctor_get(v___x_598_, 0);
lean_dec(v_unused_615_);
v___x_607_ = v___x_598_;
v_isShared_608_ = v_isSharedCheck_614_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_defEqI_604_);
lean_inc(v_congrInfo_603_);
lean_inc(v_getLevel_602_);
lean_inc(v_inferType_601_);
lean_inc(v_proofInstInfo_600_);
lean_inc(v_maxFVar_599_);
lean_dec(v___x_598_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_614_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_610_; 
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 0, v_snd_597_);
v___x_610_ = v___x_607_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v_snd_597_);
lean_ctor_set(v_reuseFailAlloc_613_, 1, v_maxFVar_599_);
lean_ctor_set(v_reuseFailAlloc_613_, 2, v_proofInstInfo_600_);
lean_ctor_set(v_reuseFailAlloc_613_, 3, v_inferType_601_);
lean_ctor_set(v_reuseFailAlloc_613_, 4, v_getLevel_602_);
lean_ctor_set(v_reuseFailAlloc_613_, 5, v_congrInfo_603_);
lean_ctor_set(v_reuseFailAlloc_613_, 6, v_defEqI_604_);
lean_ctor_set_uint8(v_reuseFailAlloc_613_, sizeof(void*)*7, v_debug_605_);
v___x_610_ = v_reuseFailAlloc_613_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_611_ = lean_st_ref_set(v_a_570_, v___x_610_);
v___x_612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_612_, 0, v_fst_596_);
return v___x_612_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM___boxed(lean_object* v_00_u03b1_618_, lean_object* v_k_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l_Lean_Meta_Sym_Internal_liftBuilderM(v_00_u03b1_618_, v_k_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_);
lean_dec(v_a_625_);
lean_dec_ref(v_a_624_);
lean_dec(v_a_623_);
lean_dec_ref(v_a_622_);
lean_dec(v_a_621_);
lean_dec_ref(v_a_620_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_share1___redArg(lean_object* v_e_628_, lean_object* v_a_629_){
_start:
{
lean_object* v___x_630_; uint64_t v___x_631_; size_t v___x_632_; lean_object* v___x_633_; uint8_t v___x_634_; 
v___x_630_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy;
v___x_631_ = l_Lean_Meta_Sym_instHashableAlphaKey___private__1(v_e_628_);
v___x_632_ = lean_uint64_to_usize(v___x_631_);
lean_inc_ref(v_e_628_);
lean_inc_ref(v_a_629_);
v___x_633_ = l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg(v_a_629_, v___x_632_, v_e_628_, v___x_630_);
v___x_634_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_633_, v___x_630_);
if (v___x_634_ == 0)
{
lean_object* v___x_635_; 
lean_dec_ref(v_e_628_);
v___x_635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_635_, 0, v___x_633_);
lean_ctor_set(v___x_635_, 1, v_a_629_);
return v___x_635_;
}
else
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
lean_dec_ref(v___x_633_);
v___x_636_ = lean_box(0);
lean_inc_ref(v_e_628_);
v___x_637_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1___redArg(v_a_629_, v_e_628_, v___x_636_);
v___x_638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_638_, 0, v_e_628_);
lean_ctor_set(v___x_638_, 1, v___x_637_);
return v___x_638_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_share1(lean_object* v_e_639_, uint8_t v_a_640_, lean_object* v_a_641_){
_start:
{
lean_object* v___x_642_; 
v___x_642_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v_e_639_, v_a_641_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_share1___boxed(lean_object* v_e_643_, lean_object* v_a_644_, lean_object* v_a_645_){
_start:
{
uint8_t v_a_1189__boxed_646_; lean_object* v_res_647_; 
v_a_1189__boxed_646_ = lean_unbox(v_a_644_);
v_res_647_ = l_Lean_Meta_Sym_Internal_Builder_share1(v_e_643_, v_a_1189__boxed_646_, v_a_645_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1(lean_object* v_msg_655_, uint8_t v___y_656_, lean_object* v___y_657_){
_start:
{
lean_object* v___f_658_; lean_object* v___f_659_; lean_object* v___f_660_; lean_object* v___f_661_; lean_object* v___f_662_; lean_object* v___f_663_; lean_object* v___f_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___f_668_; lean_object* v___f_669_; lean_object* v___f_670_; lean_object* v___f_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___f_680_; lean_object* v___x_691__overap_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
v___f_658_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__0));
v___f_659_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__1));
v___f_660_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__2));
v___f_661_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__3));
v___f_662_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__4));
v___f_663_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__5));
v___f_664_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__6));
v___x_665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_665_, 0, v___f_658_);
lean_ctor_set(v___x_665_, 1, v___f_659_);
v___x_666_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_666_, 0, v___x_665_);
lean_ctor_set(v___x_666_, 1, v___f_660_);
lean_ctor_set(v___x_666_, 2, v___f_661_);
lean_ctor_set(v___x_666_, 3, v___f_662_);
lean_ctor_set(v___x_666_, 4, v___f_663_);
v___x_667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_667_, 0, v___x_666_);
lean_ctor_set(v___x_667_, 1, v___f_664_);
lean_inc_ref(v___x_667_);
v___f_668_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_668_, 0, v___x_667_);
lean_inc_ref(v___x_667_);
v___f_669_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_669_, 0, v___x_667_);
lean_inc_ref(v___x_667_);
v___f_670_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_670_, 0, v___x_667_);
lean_inc_ref(v___x_667_);
v___f_671_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_671_, 0, v___x_667_);
lean_inc_ref(v___x_667_);
v___x_672_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_672_, 0, lean_box(0));
lean_closure_set(v___x_672_, 1, lean_box(0));
lean_closure_set(v___x_672_, 2, v___x_667_);
v___x_673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_673_, 0, v___x_672_);
lean_ctor_set(v___x_673_, 1, v___f_668_);
lean_inc_ref(v___x_667_);
v___x_674_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_674_, 0, lean_box(0));
lean_closure_set(v___x_674_, 1, lean_box(0));
lean_closure_set(v___x_674_, 2, v___x_667_);
v___x_675_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_675_, 0, v___x_673_);
lean_ctor_set(v___x_675_, 1, v___x_674_);
lean_ctor_set(v___x_675_, 2, v___f_669_);
lean_ctor_set(v___x_675_, 3, v___f_670_);
lean_ctor_set(v___x_675_, 4, v___f_671_);
v___x_676_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_676_, 0, lean_box(0));
lean_closure_set(v___x_676_, 1, lean_box(0));
lean_closure_set(v___x_676_, 2, v___x_667_);
v___x_677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_677_, 0, v___x_675_);
lean_ctor_set(v___x_677_, 1, v___x_676_);
v___x_678_ = lean_box(0);
v___x_679_ = l_instInhabitedOfMonad___redArg(v___x_677_, v___x_678_);
v___f_680_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_680_, 0, v___x_679_);
v___x_691__overap_681_ = lean_panic_fn(v___f_680_, v_msg_655_);
v___x_682_ = lean_box(v___y_656_);
v___x_683_ = lean_apply_2(v___x_691__overap_681_, v___x_682_, v___y_657_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___boxed(lean_object* v_msg_684_, lean_object* v___y_685_, lean_object* v___y_686_){
_start:
{
uint8_t v___y_816__boxed_687_; lean_object* v_res_688_; 
v___y_816__boxed_687_ = lean_unbox(v___y_685_);
v_res_688_ = l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1(v_msg_684_, v___y_816__boxed_687_, v___y_686_);
return v_res_688_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_689_, lean_object* v_i_690_, lean_object* v_k_691_){
_start:
{
lean_object* v___x_692_; uint8_t v___x_693_; 
v___x_692_ = lean_array_get_size(v_keys_689_);
v___x_693_ = lean_nat_dec_lt(v_i_690_, v___x_692_);
if (v___x_693_ == 0)
{
lean_dec_ref(v_k_691_);
lean_dec(v_i_690_);
return v___x_693_;
}
else
{
lean_object* v_k_x27_694_; uint8_t v___x_695_; 
v_k_x27_694_ = lean_array_fget_borrowed(v_keys_689_, v_i_690_);
lean_inc(v_k_x27_694_);
lean_inc_ref(v_k_691_);
v___x_695_ = l_Lean_Meta_Sym_instBEqAlphaKey___private__1(v_k_691_, v_k_x27_694_);
if (v___x_695_ == 0)
{
lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_696_ = lean_unsigned_to_nat(1u);
v___x_697_ = lean_nat_add(v_i_690_, v___x_696_);
lean_dec(v_i_690_);
v_i_690_ = v___x_697_;
goto _start;
}
else
{
lean_dec_ref(v_k_691_);
lean_dec(v_i_690_);
return v___x_695_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_699_, lean_object* v_i_700_, lean_object* v_k_701_){
_start:
{
uint8_t v_res_702_; lean_object* v_r_703_; 
v_res_702_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg(v_keys_699_, v_i_700_, v_k_701_);
lean_dec_ref(v_keys_699_);
v_r_703_ = lean_box(v_res_702_);
return v_r_703_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg(lean_object* v_x_704_, size_t v_x_705_, lean_object* v_x_706_){
_start:
{
if (lean_obj_tag(v_x_704_) == 0)
{
lean_object* v_es_707_; lean_object* v___x_708_; size_t v___x_709_; size_t v___x_710_; size_t v___x_711_; lean_object* v_j_712_; lean_object* v___x_713_; 
v_es_707_ = lean_ctor_get(v_x_704_, 0);
lean_inc_ref(v_es_707_);
lean_dec_ref(v_x_704_);
v___x_708_ = lean_box(2);
v___x_709_ = ((size_t)5ULL);
v___x_710_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__1);
v___x_711_ = lean_usize_land(v_x_705_, v___x_710_);
v_j_712_ = lean_usize_to_nat(v___x_711_);
v___x_713_ = lean_array_get(v___x_708_, v_es_707_, v_j_712_);
lean_dec(v_j_712_);
lean_dec_ref(v_es_707_);
switch(lean_obj_tag(v___x_713_))
{
case 0:
{
lean_object* v_key_714_; uint8_t v___x_715_; 
v_key_714_ = lean_ctor_get(v___x_713_, 0);
lean_inc(v_key_714_);
lean_dec_ref(v___x_713_);
v___x_715_ = l_Lean_Meta_Sym_instBEqAlphaKey___private__1(v_x_706_, v_key_714_);
return v___x_715_;
}
case 1:
{
lean_object* v_node_716_; size_t v___x_717_; 
v_node_716_ = lean_ctor_get(v___x_713_, 0);
lean_inc(v_node_716_);
lean_dec_ref(v___x_713_);
v___x_717_ = lean_usize_shift_right(v_x_705_, v___x_709_);
v_x_704_ = v_node_716_;
v_x_705_ = v___x_717_;
goto _start;
}
default: 
{
uint8_t v___x_719_; 
lean_dec_ref(v_x_706_);
v___x_719_ = 0;
return v___x_719_;
}
}
}
else
{
lean_object* v_ks_720_; lean_object* v___x_721_; uint8_t v___x_722_; 
v_ks_720_ = lean_ctor_get(v_x_704_, 0);
lean_inc_ref(v_ks_720_);
lean_dec_ref(v_x_704_);
v___x_721_ = lean_unsigned_to_nat(0u);
v___x_722_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg(v_ks_720_, v___x_721_, v_x_706_);
lean_dec_ref(v_ks_720_);
return v___x_722_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg___boxed(lean_object* v_x_723_, lean_object* v_x_724_, lean_object* v_x_725_){
_start:
{
size_t v_x_898__boxed_726_; uint8_t v_res_727_; lean_object* v_r_728_; 
v_x_898__boxed_726_ = lean_unbox_usize(v_x_724_);
lean_dec(v_x_724_);
v_res_727_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg(v_x_723_, v_x_898__boxed_726_, v_x_725_);
v_r_728_ = lean_box(v_res_727_);
return v_r_728_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg(lean_object* v_x_729_, lean_object* v_x_730_){
_start:
{
uint64_t v___x_731_; size_t v___x_732_; uint8_t v___x_733_; 
v___x_731_ = l_Lean_Meta_Sym_instHashableAlphaKey___private__1(v_x_730_);
v___x_732_ = lean_uint64_to_usize(v___x_731_);
v___x_733_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg(v_x_729_, v___x_732_, v_x_730_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg___boxed(lean_object* v_x_734_, lean_object* v_x_735_){
_start:
{
uint8_t v_res_736_; lean_object* v_r_737_; 
v_res_736_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg(v_x_734_, v_x_735_);
v_r_737_ = lean_box(v_res_736_);
return v_r_737_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__2(void){
_start:
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_740_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__1));
v___x_741_ = lean_unsigned_to_nat(2u);
v___x_742_ = lean_unsigned_to_nat(74u);
v___x_743_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__0));
v___x_744_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_745_ = l_mkPanicMessageWithDecl(v___x_744_, v___x_743_, v___x_742_, v___x_741_, v___x_740_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_assertShared(lean_object* v_e_746_, uint8_t v_a_747_, lean_object* v_a_748_){
_start:
{
uint8_t v___x_749_; 
lean_inc_ref(v_a_748_);
v___x_749_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg(v_a_748_, v_e_746_);
if (v___x_749_ == 0)
{
lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_750_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__2, &l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__2_once, _init_l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__2);
v___x_751_ = l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1(v___x_750_, v_a_747_, v_a_748_);
return v___x_751_;
}
else
{
lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_752_ = lean_box(0);
v___x_753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_753_, 0, v___x_752_);
lean_ctor_set(v___x_753_, 1, v_a_748_);
return v___x_753_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_assertShared___boxed(lean_object* v_e_754_, lean_object* v_a_755_, lean_object* v_a_756_){
_start:
{
uint8_t v_a_969__boxed_757_; lean_object* v_res_758_; 
v_a_969__boxed_757_ = lean_unbox(v_a_755_);
v_res_758_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_e_754_, v_a_969__boxed_757_, v_a_756_);
return v_res_758_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0(lean_object* v_00_u03b2_759_, lean_object* v_x_760_, lean_object* v_x_761_){
_start:
{
uint8_t v___x_762_; 
v___x_762_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg(v_x_760_, v_x_761_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___boxed(lean_object* v_00_u03b2_763_, lean_object* v_x_764_, lean_object* v_x_765_){
_start:
{
uint8_t v_res_766_; lean_object* v_r_767_; 
v_res_766_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0(v_00_u03b2_763_, v_x_764_, v_x_765_);
v_r_767_ = lean_box(v_res_766_);
return v_r_767_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0(lean_object* v_00_u03b2_768_, lean_object* v_x_769_, size_t v_x_770_, lean_object* v_x_771_){
_start:
{
uint8_t v___x_772_; 
v___x_772_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg(v_x_769_, v_x_770_, v_x_771_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___boxed(lean_object* v_00_u03b2_773_, lean_object* v_x_774_, lean_object* v_x_775_, lean_object* v_x_776_){
_start:
{
size_t v_x_1002__boxed_777_; uint8_t v_res_778_; lean_object* v_r_779_; 
v_x_1002__boxed_777_ = lean_unbox_usize(v_x_775_);
lean_dec(v_x_775_);
v_res_778_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0(v_00_u03b2_773_, v_x_774_, v_x_1002__boxed_777_, v_x_776_);
v_r_779_ = lean_box(v_res_778_);
return v_r_779_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_780_, lean_object* v_keys_781_, lean_object* v_vals_782_, lean_object* v_heq_783_, lean_object* v_i_784_, lean_object* v_k_785_){
_start:
{
uint8_t v___x_786_; 
v___x_786_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg(v_keys_781_, v_i_784_, v_k_785_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_787_, lean_object* v_keys_788_, lean_object* v_vals_789_, lean_object* v_heq_790_, lean_object* v_i_791_, lean_object* v_k_792_){
_start:
{
uint8_t v_res_793_; lean_object* v_r_794_; 
v_res_793_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2(v_00_u03b2_787_, v_keys_788_, v_vals_789_, v_heq_790_, v_i_791_, v_k_792_);
lean_dec_ref(v_vals_789_);
lean_dec_ref(v_keys_788_);
v_r_794_ = lean_box(v_res_793_);
return v_r_794_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM(void){
_start:
{
lean_object* v___f_797_; lean_object* v___f_798_; lean_object* v___f_799_; lean_object* v___f_800_; lean_object* v___f_801_; lean_object* v___f_802_; lean_object* v___f_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___f_807_; lean_object* v___f_808_; lean_object* v___f_809_; lean_object* v___f_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
v___f_797_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__0));
v___f_798_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__1));
v___f_799_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__2));
v___f_800_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__3));
v___f_801_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__4));
v___f_802_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__5));
v___f_803_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__6));
v___x_804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_804_, 0, v___f_797_);
lean_ctor_set(v___x_804_, 1, v___f_798_);
v___x_805_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_805_, 0, v___x_804_);
lean_ctor_set(v___x_805_, 1, v___f_799_);
lean_ctor_set(v___x_805_, 2, v___f_800_);
lean_ctor_set(v___x_805_, 3, v___f_801_);
lean_ctor_set(v___x_805_, 4, v___f_802_);
v___x_806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_806_, 0, v___x_805_);
lean_ctor_set(v___x_806_, 1, v___f_803_);
lean_inc_ref(v___x_806_);
v___f_807_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_807_, 0, v___x_806_);
lean_inc_ref(v___x_806_);
v___f_808_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_808_, 0, v___x_806_);
lean_inc_ref(v___x_806_);
v___f_809_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_809_, 0, v___x_806_);
lean_inc_ref(v___x_806_);
v___f_810_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_810_, 0, v___x_806_);
lean_inc_ref(v___x_806_);
v___x_811_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_811_, 0, lean_box(0));
lean_closure_set(v___x_811_, 1, lean_box(0));
lean_closure_set(v___x_811_, 2, v___x_806_);
v___x_812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_812_, 0, v___x_811_);
lean_ctor_set(v___x_812_, 1, v___f_807_);
lean_inc_ref(v___x_806_);
v___x_813_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_813_, 0, lean_box(0));
lean_closure_set(v___x_813_, 1, lean_box(0));
lean_closure_set(v___x_813_, 2, v___x_806_);
v___x_814_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_814_, 0, v___x_812_);
lean_ctor_set(v___x_814_, 1, v___x_813_);
lean_ctor_set(v___x_814_, 2, v___f_808_);
lean_ctor_set(v___x_814_, 3, v___f_809_);
lean_ctor_set(v___x_814_, 4, v___f_810_);
v___x_815_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_815_, 0, lean_box(0));
lean_closure_set(v___x_815_, 1, lean_box(0));
lean_closure_set(v___x_815_, 2, v___x_806_);
v___x_816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_816_, 0, v___x_814_);
lean_ctor_set(v___x_816_, 1, v___x_815_);
v___x_817_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__0));
v___x_818_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__1));
v___x_819_ = lean_alloc_closure((void*)(l_ReaderT_read), 4, 3);
lean_closure_set(v___x_819_, 0, lean_box(0));
lean_closure_set(v___x_819_, 1, lean_box(0));
lean_closure_set(v___x_819_, 2, v___x_816_);
v___x_820_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_820_, 0, v___x_817_);
lean_ctor_set(v___x_820_, 1, v___x_818_);
lean_ctor_set(v___x_820_, 2, v___x_819_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLitS___redArg(lean_object* v_inst_821_, lean_object* v_l_822_){
_start:
{
lean_object* v_share1_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
v_share1_823_ = lean_ctor_get(v_inst_821_, 0);
lean_inc(v_share1_823_);
lean_dec_ref(v_inst_821_);
v___x_824_ = l_Lean_Expr_lit___override(v_l_822_);
v___x_825_ = lean_apply_1(v_share1_823_, v___x_824_);
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLitS(lean_object* v_m_826_, lean_object* v_inst_827_, lean_object* v_l_828_){
_start:
{
lean_object* v___x_829_; 
v___x_829_ = l_Lean_Meta_Sym_Internal_mkLitS___redArg(v_inst_827_, v_l_828_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___redArg(lean_object* v_inst_830_, lean_object* v_declName_831_, lean_object* v_us_832_){
_start:
{
lean_object* v_share1_833_; lean_object* v___x_834_; lean_object* v___x_835_; 
v_share1_833_ = lean_ctor_get(v_inst_830_, 0);
lean_inc(v_share1_833_);
lean_dec_ref(v_inst_830_);
v___x_834_ = l_Lean_Expr_const___override(v_declName_831_, v_us_832_);
v___x_835_ = lean_apply_1(v_share1_833_, v___x_834_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS(lean_object* v_m_836_, lean_object* v_inst_837_, lean_object* v_declName_838_, lean_object* v_us_839_){
_start:
{
lean_object* v___x_840_; 
v___x_840_ = l_Lean_Meta_Sym_Internal_mkConstS___redArg(v_inst_837_, v_declName_838_, v_us_839_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___redArg(lean_object* v_inst_841_, lean_object* v_idx_842_){
_start:
{
lean_object* v_share1_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
v_share1_843_ = lean_ctor_get(v_inst_841_, 0);
lean_inc(v_share1_843_);
lean_dec_ref(v_inst_841_);
v___x_844_ = l_Lean_Expr_bvar___override(v_idx_842_);
v___x_845_ = lean_apply_1(v_share1_843_, v___x_844_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS(lean_object* v_m_846_, lean_object* v_inst_847_, lean_object* v_idx_848_){
_start:
{
lean_object* v___x_849_; 
v___x_849_ = l_Lean_Meta_Sym_Internal_mkBVarS___redArg(v_inst_847_, v_idx_848_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS___redArg(lean_object* v_inst_850_, lean_object* v_u_851_){
_start:
{
lean_object* v_share1_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
v_share1_852_ = lean_ctor_get(v_inst_850_, 0);
lean_inc(v_share1_852_);
lean_dec_ref(v_inst_850_);
v___x_853_ = l_Lean_Expr_sort___override(v_u_851_);
v___x_854_ = lean_apply_1(v_share1_852_, v___x_853_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS(lean_object* v_m_855_, lean_object* v_inst_856_, lean_object* v_u_857_){
_start:
{
lean_object* v___x_858_; 
v___x_858_ = l_Lean_Meta_Sym_Internal_mkSortS___redArg(v_inst_856_, v_u_857_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___redArg(lean_object* v_inst_859_, lean_object* v_fvarId_860_){
_start:
{
lean_object* v_share1_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
v_share1_861_ = lean_ctor_get(v_inst_859_, 0);
lean_inc(v_share1_861_);
lean_dec_ref(v_inst_859_);
v___x_862_ = l_Lean_Expr_fvar___override(v_fvarId_860_);
v___x_863_ = lean_apply_1(v_share1_861_, v___x_862_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS(lean_object* v_m_864_, lean_object* v_inst_865_, lean_object* v_fvarId_866_){
_start:
{
lean_object* v___x_867_; 
v___x_867_ = l_Lean_Meta_Sym_Internal_mkFVarS___redArg(v_inst_865_, v_fvarId_866_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMVarS___redArg(lean_object* v_inst_868_, lean_object* v_mvarId_869_){
_start:
{
lean_object* v_share1_870_; lean_object* v___x_871_; lean_object* v___x_872_; 
v_share1_870_ = lean_ctor_get(v_inst_868_, 0);
lean_inc(v_share1_870_);
lean_dec_ref(v_inst_868_);
v___x_871_ = l_Lean_Expr_mvar___override(v_mvarId_869_);
v___x_872_ = lean_apply_1(v_share1_870_, v___x_871_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMVarS(lean_object* v_m_873_, lean_object* v_inst_874_, lean_object* v_mvarId_875_){
_start:
{
lean_object* v___x_876_; 
v___x_876_ = l_Lean_Meta_Sym_Internal_mkMVarS___redArg(v_inst_874_, v_mvarId_875_);
return v___x_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__0(lean_object* v_d_877_, lean_object* v_e_878_, lean_object* v_share1_879_, lean_object* v_____r_880_){
_start:
{
lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_881_ = l_Lean_Expr_mdata___override(v_d_877_, v_e_878_);
v___x_882_ = lean_apply_1(v_share1_879_, v___x_881_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1(lean_object* v___f_883_, lean_object* v_____r_884_){
_start:
{
lean_object* v___x_885_; 
v___x_885_ = lean_apply_1(v___f_883_, v_____r_884_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__2(lean_object* v___f_886_, lean_object* v_assertShared_887_, lean_object* v_e_888_, lean_object* v_toBind_889_, lean_object* v___f_890_, uint8_t v_____do__lift_891_){
_start:
{
if (v_____do__lift_891_ == 0)
{
lean_object* v___x_892_; lean_object* v___x_893_; 
lean_dec(v___f_890_);
lean_dec(v_toBind_889_);
lean_dec_ref(v_e_888_);
lean_dec(v_assertShared_887_);
v___x_892_ = lean_box(0);
v___x_893_ = lean_apply_1(v___f_886_, v___x_892_);
return v___x_893_;
}
else
{
lean_object* v___x_894_; lean_object* v___x_895_; 
lean_dec(v___f_886_);
v___x_894_ = lean_apply_1(v_assertShared_887_, v_e_888_);
v___x_895_ = lean_apply_4(v_toBind_889_, lean_box(0), lean_box(0), v___x_894_, v___f_890_);
return v___x_895_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__2___boxed(lean_object* v___f_896_, lean_object* v_assertShared_897_, lean_object* v_e_898_, lean_object* v_toBind_899_, lean_object* v___f_900_, lean_object* v_____do__lift_901_){
_start:
{
uint8_t v_____do__lift_85__boxed_902_; lean_object* v_res_903_; 
v_____do__lift_85__boxed_902_ = lean_unbox(v_____do__lift_901_);
v_res_903_ = l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__2(v___f_896_, v_assertShared_897_, v_e_898_, v_toBind_899_, v___f_900_, v_____do__lift_85__boxed_902_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg(lean_object* v_inst_904_, lean_object* v_inst_905_, lean_object* v_d_906_, lean_object* v_e_907_){
_start:
{
lean_object* v_toBind_908_; lean_object* v_share1_909_; lean_object* v_assertShared_910_; lean_object* v_isDebugEnabled_911_; lean_object* v___f_912_; lean_object* v___f_913_; lean_object* v___f_914_; lean_object* v___x_915_; 
v_toBind_908_ = lean_ctor_get(v_inst_905_, 1);
lean_inc(v_toBind_908_);
lean_dec_ref(v_inst_905_);
v_share1_909_ = lean_ctor_get(v_inst_904_, 0);
lean_inc(v_share1_909_);
v_assertShared_910_ = lean_ctor_get(v_inst_904_, 1);
lean_inc(v_assertShared_910_);
v_isDebugEnabled_911_ = lean_ctor_get(v_inst_904_, 2);
lean_inc(v_isDebugEnabled_911_);
lean_dec_ref(v_inst_904_);
lean_inc_ref(v_e_907_);
v___f_912_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__0), 4, 3);
lean_closure_set(v___f_912_, 0, v_d_906_);
lean_closure_set(v___f_912_, 1, v_e_907_);
lean_closure_set(v___f_912_, 2, v_share1_909_);
lean_inc_ref(v___f_912_);
v___f_913_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_913_, 0, v___f_912_);
lean_inc(v_toBind_908_);
v___f_914_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_914_, 0, v___f_912_);
lean_closure_set(v___f_914_, 1, v_assertShared_910_);
lean_closure_set(v___f_914_, 2, v_e_907_);
lean_closure_set(v___f_914_, 3, v_toBind_908_);
lean_closure_set(v___f_914_, 4, v___f_913_);
v___x_915_ = lean_apply_4(v_toBind_908_, lean_box(0), lean_box(0), v_isDebugEnabled_911_, v___f_914_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS(lean_object* v_m_916_, lean_object* v_inst_917_, lean_object* v_inst_918_, lean_object* v_d_919_, lean_object* v_e_920_){
_start:
{
lean_object* v___x_921_; 
v___x_921_ = l_Lean_Meta_Sym_Internal_mkMDataS___redArg(v_inst_917_, v_inst_918_, v_d_919_, v_e_920_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__0(lean_object* v_structName_922_, lean_object* v_idx_923_, lean_object* v_struct_924_, lean_object* v_share1_925_, lean_object* v_____r_926_){
_start:
{
lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_927_ = l_Lean_Expr_proj___override(v_structName_922_, v_idx_923_, v_struct_924_);
v___x_928_ = lean_apply_1(v_share1_925_, v___x_927_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__2(lean_object* v___f_929_, lean_object* v_assertShared_930_, lean_object* v_struct_931_, lean_object* v_toBind_932_, lean_object* v___f_933_, uint8_t v_____do__lift_934_){
_start:
{
if (v_____do__lift_934_ == 0)
{
lean_object* v___x_935_; lean_object* v___x_936_; 
lean_dec(v___f_933_);
lean_dec(v_toBind_932_);
lean_dec_ref(v_struct_931_);
lean_dec(v_assertShared_930_);
v___x_935_ = lean_box(0);
v___x_936_ = lean_apply_1(v___f_929_, v___x_935_);
return v___x_936_;
}
else
{
lean_object* v___x_937_; lean_object* v___x_938_; 
lean_dec(v___f_929_);
v___x_937_ = lean_apply_1(v_assertShared_930_, v_struct_931_);
v___x_938_ = lean_apply_4(v_toBind_932_, lean_box(0), lean_box(0), v___x_937_, v___f_933_);
return v___x_938_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__2___boxed(lean_object* v___f_939_, lean_object* v_assertShared_940_, lean_object* v_struct_941_, lean_object* v_toBind_942_, lean_object* v___f_943_, lean_object* v_____do__lift_944_){
_start:
{
uint8_t v_____do__lift_79__boxed_945_; lean_object* v_res_946_; 
v_____do__lift_79__boxed_945_ = lean_unbox(v_____do__lift_944_);
v_res_946_ = l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__2(v___f_939_, v_assertShared_940_, v_struct_941_, v_toBind_942_, v___f_943_, v_____do__lift_79__boxed_945_);
return v_res_946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___redArg(lean_object* v_inst_947_, lean_object* v_inst_948_, lean_object* v_structName_949_, lean_object* v_idx_950_, lean_object* v_struct_951_){
_start:
{
lean_object* v_toBind_952_; lean_object* v_share1_953_; lean_object* v_assertShared_954_; lean_object* v_isDebugEnabled_955_; lean_object* v___f_956_; lean_object* v___f_957_; lean_object* v___f_958_; lean_object* v___x_959_; 
v_toBind_952_ = lean_ctor_get(v_inst_948_, 1);
lean_inc(v_toBind_952_);
lean_dec_ref(v_inst_948_);
v_share1_953_ = lean_ctor_get(v_inst_947_, 0);
lean_inc(v_share1_953_);
v_assertShared_954_ = lean_ctor_get(v_inst_947_, 1);
lean_inc(v_assertShared_954_);
v_isDebugEnabled_955_ = lean_ctor_get(v_inst_947_, 2);
lean_inc(v_isDebugEnabled_955_);
lean_dec_ref(v_inst_947_);
lean_inc_ref(v_struct_951_);
v___f_956_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__0), 5, 4);
lean_closure_set(v___f_956_, 0, v_structName_949_);
lean_closure_set(v___f_956_, 1, v_idx_950_);
lean_closure_set(v___f_956_, 2, v_struct_951_);
lean_closure_set(v___f_956_, 3, v_share1_953_);
lean_inc_ref(v___f_956_);
v___f_957_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_957_, 0, v___f_956_);
lean_inc(v_toBind_952_);
v___f_958_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_958_, 0, v___f_956_);
lean_closure_set(v___f_958_, 1, v_assertShared_954_);
lean_closure_set(v___f_958_, 2, v_struct_951_);
lean_closure_set(v___f_958_, 3, v_toBind_952_);
lean_closure_set(v___f_958_, 4, v___f_957_);
v___x_959_ = lean_apply_4(v_toBind_952_, lean_box(0), lean_box(0), v_isDebugEnabled_955_, v___f_958_);
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS(lean_object* v_m_960_, lean_object* v_inst_961_, lean_object* v_inst_962_, lean_object* v_structName_963_, lean_object* v_idx_964_, lean_object* v_struct_965_){
_start:
{
lean_object* v___x_966_; 
v___x_966_ = l_Lean_Meta_Sym_Internal_mkProjS___redArg(v_inst_961_, v_inst_962_, v_structName_963_, v_idx_964_, v_struct_965_);
return v___x_966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__0(lean_object* v_f_967_, lean_object* v_a_968_, lean_object* v_share1_969_, lean_object* v_____r_970_){
_start:
{
lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_971_ = l_Lean_Expr_app___override(v_f_967_, v_a_968_);
v___x_972_ = lean_apply_1(v_share1_969_, v___x_971_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__2(lean_object* v_assertShared_973_, lean_object* v_a_974_, lean_object* v_toBind_975_, lean_object* v___f_976_, lean_object* v_____r_977_){
_start:
{
lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_978_ = lean_apply_1(v_assertShared_973_, v_a_974_);
v___x_979_ = lean_apply_4(v_toBind_975_, lean_box(0), lean_box(0), v___x_978_, v___f_976_);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__1(lean_object* v___f_980_, lean_object* v_assertShared_981_, lean_object* v_a_982_, lean_object* v_toBind_983_, lean_object* v___f_984_, lean_object* v_f_985_, uint8_t v_____do__lift_986_){
_start:
{
if (v_____do__lift_986_ == 0)
{
lean_object* v___x_987_; lean_object* v___x_988_; 
lean_dec_ref(v_f_985_);
lean_dec(v___f_984_);
lean_dec(v_toBind_983_);
lean_dec_ref(v_a_982_);
lean_dec(v_assertShared_981_);
v___x_987_ = lean_box(0);
v___x_988_ = lean_apply_1(v___f_980_, v___x_987_);
return v___x_988_;
}
else
{
lean_object* v___f_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
lean_dec(v___f_980_);
lean_inc(v_toBind_983_);
lean_inc(v_assertShared_981_);
v___f_989_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__2), 5, 4);
lean_closure_set(v___f_989_, 0, v_assertShared_981_);
lean_closure_set(v___f_989_, 1, v_a_982_);
lean_closure_set(v___f_989_, 2, v_toBind_983_);
lean_closure_set(v___f_989_, 3, v___f_984_);
v___x_990_ = lean_apply_1(v_assertShared_981_, v_f_985_);
v___x_991_ = lean_apply_4(v_toBind_983_, lean_box(0), lean_box(0), v___x_990_, v___f_989_);
return v___x_991_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__1___boxed(lean_object* v___f_992_, lean_object* v_assertShared_993_, lean_object* v_a_994_, lean_object* v_toBind_995_, lean_object* v___f_996_, lean_object* v_f_997_, lean_object* v_____do__lift_998_){
_start:
{
uint8_t v_____do__lift_104__boxed_999_; lean_object* v_res_1000_; 
v_____do__lift_104__boxed_999_ = lean_unbox(v_____do__lift_998_);
v_res_1000_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__1(v___f_992_, v_assertShared_993_, v_a_994_, v_toBind_995_, v___f_996_, v_f_997_, v_____do__lift_104__boxed_999_);
return v_res_1000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg(lean_object* v_inst_1001_, lean_object* v_inst_1002_, lean_object* v_f_1003_, lean_object* v_a_1004_){
_start:
{
lean_object* v_toBind_1005_; lean_object* v_share1_1006_; lean_object* v_assertShared_1007_; lean_object* v_isDebugEnabled_1008_; lean_object* v___f_1009_; lean_object* v___f_1010_; lean_object* v___f_1011_; lean_object* v___x_1012_; 
v_toBind_1005_ = lean_ctor_get(v_inst_1002_, 1);
lean_inc(v_toBind_1005_);
lean_dec_ref(v_inst_1002_);
v_share1_1006_ = lean_ctor_get(v_inst_1001_, 0);
lean_inc(v_share1_1006_);
v_assertShared_1007_ = lean_ctor_get(v_inst_1001_, 1);
lean_inc(v_assertShared_1007_);
v_isDebugEnabled_1008_ = lean_ctor_get(v_inst_1001_, 2);
lean_inc(v_isDebugEnabled_1008_);
lean_dec_ref(v_inst_1001_);
lean_inc_ref(v_a_1004_);
lean_inc_ref(v_f_1003_);
v___f_1009_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1009_, 0, v_f_1003_);
lean_closure_set(v___f_1009_, 1, v_a_1004_);
lean_closure_set(v___f_1009_, 2, v_share1_1006_);
lean_inc_ref(v___f_1009_);
v___f_1010_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1010_, 0, v___f_1009_);
lean_inc(v_toBind_1005_);
v___f_1011_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_1011_, 0, v___f_1009_);
lean_closure_set(v___f_1011_, 1, v_assertShared_1007_);
lean_closure_set(v___f_1011_, 2, v_a_1004_);
lean_closure_set(v___f_1011_, 3, v_toBind_1005_);
lean_closure_set(v___f_1011_, 4, v___f_1010_);
lean_closure_set(v___f_1011_, 5, v_f_1003_);
v___x_1012_ = lean_apply_4(v_toBind_1005_, lean_box(0), lean_box(0), v_isDebugEnabled_1008_, v___f_1011_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS(lean_object* v_m_1013_, lean_object* v_inst_1014_, lean_object* v_inst_1015_, lean_object* v_f_1016_, lean_object* v_a_1017_){
_start:
{
lean_object* v___x_1018_; 
v___x_1018_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1014_, v_inst_1015_, v_f_1016_, v_a_1017_);
return v___x_1018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__0(lean_object* v_x_1019_, lean_object* v_t_1020_, lean_object* v_b_1021_, uint8_t v_bi_1022_, lean_object* v_share1_1023_, lean_object* v_____r_1024_){
_start:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1025_ = l_Lean_Expr_lam___override(v_x_1019_, v_t_1020_, v_b_1021_, v_bi_1022_);
v___x_1026_ = lean_apply_1(v_share1_1023_, v___x_1025_);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__0___boxed(lean_object* v_x_1027_, lean_object* v_t_1028_, lean_object* v_b_1029_, lean_object* v_bi_1030_, lean_object* v_share1_1031_, lean_object* v_____r_1032_){
_start:
{
uint8_t v_bi_boxed_1033_; lean_object* v_res_1034_; 
v_bi_boxed_1033_ = lean_unbox(v_bi_1030_);
v_res_1034_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__0(v_x_1027_, v_t_1028_, v_b_1029_, v_bi_boxed_1033_, v_share1_1031_, v_____r_1032_);
return v_res_1034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__2(lean_object* v_assertShared_1035_, lean_object* v_b_1036_, lean_object* v_toBind_1037_, lean_object* v___f_1038_, lean_object* v_____r_1039_){
_start:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1040_ = lean_apply_1(v_assertShared_1035_, v_b_1036_);
v___x_1041_ = lean_apply_4(v_toBind_1037_, lean_box(0), lean_box(0), v___x_1040_, v___f_1038_);
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1(lean_object* v___f_1042_, lean_object* v_assertShared_1043_, lean_object* v_b_1044_, lean_object* v_toBind_1045_, lean_object* v___f_1046_, lean_object* v_t_1047_, uint8_t v_____do__lift_1048_){
_start:
{
if (v_____do__lift_1048_ == 0)
{
lean_object* v___x_1049_; lean_object* v___x_1050_; 
lean_dec_ref(v_t_1047_);
lean_dec(v___f_1046_);
lean_dec(v_toBind_1045_);
lean_dec_ref(v_b_1044_);
lean_dec(v_assertShared_1043_);
v___x_1049_ = lean_box(0);
v___x_1050_ = lean_apply_1(v___f_1042_, v___x_1049_);
return v___x_1050_;
}
else
{
lean_object* v___f_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; 
lean_dec(v___f_1042_);
lean_inc(v_toBind_1045_);
lean_inc(v_assertShared_1043_);
v___f_1051_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__2), 5, 4);
lean_closure_set(v___f_1051_, 0, v_assertShared_1043_);
lean_closure_set(v___f_1051_, 1, v_b_1044_);
lean_closure_set(v___f_1051_, 2, v_toBind_1045_);
lean_closure_set(v___f_1051_, 3, v___f_1046_);
v___x_1052_ = lean_apply_1(v_assertShared_1043_, v_t_1047_);
v___x_1053_ = lean_apply_4(v_toBind_1045_, lean_box(0), lean_box(0), v___x_1052_, v___f_1051_);
return v___x_1053_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1___boxed(lean_object* v___f_1054_, lean_object* v_assertShared_1055_, lean_object* v_b_1056_, lean_object* v_toBind_1057_, lean_object* v___f_1058_, lean_object* v_t_1059_, lean_object* v_____do__lift_1060_){
_start:
{
uint8_t v_____do__lift_105__boxed_1061_; lean_object* v_res_1062_; 
v_____do__lift_105__boxed_1061_ = lean_unbox(v_____do__lift_1060_);
v_res_1062_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1(v___f_1054_, v_assertShared_1055_, v_b_1056_, v_toBind_1057_, v___f_1058_, v_t_1059_, v_____do__lift_105__boxed_1061_);
return v_res_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(lean_object* v_inst_1063_, lean_object* v_inst_1064_, lean_object* v_x_1065_, uint8_t v_bi_1066_, lean_object* v_t_1067_, lean_object* v_b_1068_){
_start:
{
lean_object* v_toBind_1069_; lean_object* v_share1_1070_; lean_object* v_assertShared_1071_; lean_object* v_isDebugEnabled_1072_; lean_object* v___x_1073_; lean_object* v___f_1074_; lean_object* v___f_1075_; lean_object* v___f_1076_; lean_object* v___x_1077_; 
v_toBind_1069_ = lean_ctor_get(v_inst_1064_, 1);
lean_inc(v_toBind_1069_);
lean_dec_ref(v_inst_1064_);
v_share1_1070_ = lean_ctor_get(v_inst_1063_, 0);
lean_inc(v_share1_1070_);
v_assertShared_1071_ = lean_ctor_get(v_inst_1063_, 1);
lean_inc(v_assertShared_1071_);
v_isDebugEnabled_1072_ = lean_ctor_get(v_inst_1063_, 2);
lean_inc(v_isDebugEnabled_1072_);
lean_dec_ref(v_inst_1063_);
v___x_1073_ = lean_box(v_bi_1066_);
lean_inc_ref(v_b_1068_);
lean_inc_ref(v_t_1067_);
v___f_1074_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1074_, 0, v_x_1065_);
lean_closure_set(v___f_1074_, 1, v_t_1067_);
lean_closure_set(v___f_1074_, 2, v_b_1068_);
lean_closure_set(v___f_1074_, 3, v___x_1073_);
lean_closure_set(v___f_1074_, 4, v_share1_1070_);
lean_inc_ref(v___f_1074_);
v___f_1075_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1075_, 0, v___f_1074_);
lean_inc(v_toBind_1069_);
v___f_1076_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_1076_, 0, v___f_1074_);
lean_closure_set(v___f_1076_, 1, v_assertShared_1071_);
lean_closure_set(v___f_1076_, 2, v_b_1068_);
lean_closure_set(v___f_1076_, 3, v_toBind_1069_);
lean_closure_set(v___f_1076_, 4, v___f_1075_);
lean_closure_set(v___f_1076_, 5, v_t_1067_);
v___x_1077_ = lean_apply_4(v_toBind_1069_, lean_box(0), lean_box(0), v_isDebugEnabled_1072_, v___f_1076_);
return v___x_1077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___boxed(lean_object* v_inst_1078_, lean_object* v_inst_1079_, lean_object* v_x_1080_, lean_object* v_bi_1081_, lean_object* v_t_1082_, lean_object* v_b_1083_){
_start:
{
uint8_t v_bi_boxed_1084_; lean_object* v_res_1085_; 
v_bi_boxed_1084_ = lean_unbox(v_bi_1081_);
v_res_1085_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v_inst_1078_, v_inst_1079_, v_x_1080_, v_bi_boxed_1084_, v_t_1082_, v_b_1083_);
return v_res_1085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS(lean_object* v_m_1086_, lean_object* v_inst_1087_, lean_object* v_inst_1088_, lean_object* v_x_1089_, uint8_t v_bi_1090_, lean_object* v_t_1091_, lean_object* v_b_1092_){
_start:
{
lean_object* v___x_1093_; 
v___x_1093_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v_inst_1087_, v_inst_1088_, v_x_1089_, v_bi_1090_, v_t_1091_, v_b_1092_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___boxed(lean_object* v_m_1094_, lean_object* v_inst_1095_, lean_object* v_inst_1096_, lean_object* v_x_1097_, lean_object* v_bi_1098_, lean_object* v_t_1099_, lean_object* v_b_1100_){
_start:
{
uint8_t v_bi_boxed_1101_; lean_object* v_res_1102_; 
v_bi_boxed_1101_ = lean_unbox(v_bi_1098_);
v_res_1102_ = l_Lean_Meta_Sym_Internal_mkLambdaS(v_m_1094_, v_inst_1095_, v_inst_1096_, v_x_1097_, v_bi_boxed_1101_, v_t_1099_, v_b_1100_);
return v_res_1102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___redArg___lam__0(lean_object* v_x_1103_, lean_object* v_t_1104_, lean_object* v_b_1105_, uint8_t v_bi_1106_, lean_object* v_share1_1107_, lean_object* v_____r_1108_){
_start:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1109_ = l_Lean_Expr_forallE___override(v_x_1103_, v_t_1104_, v_b_1105_, v_bi_1106_);
v___x_1110_ = lean_apply_1(v_share1_1107_, v___x_1109_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___redArg___lam__0___boxed(lean_object* v_x_1111_, lean_object* v_t_1112_, lean_object* v_b_1113_, lean_object* v_bi_1114_, lean_object* v_share1_1115_, lean_object* v_____r_1116_){
_start:
{
uint8_t v_bi_boxed_1117_; lean_object* v_res_1118_; 
v_bi_boxed_1117_ = lean_unbox(v_bi_1114_);
v_res_1118_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg___lam__0(v_x_1111_, v_t_1112_, v_b_1113_, v_bi_boxed_1117_, v_share1_1115_, v_____r_1116_);
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___redArg(lean_object* v_inst_1119_, lean_object* v_inst_1120_, lean_object* v_x_1121_, uint8_t v_bi_1122_, lean_object* v_t_1123_, lean_object* v_b_1124_){
_start:
{
lean_object* v_toBind_1125_; lean_object* v_share1_1126_; lean_object* v_assertShared_1127_; lean_object* v_isDebugEnabled_1128_; lean_object* v___x_1129_; lean_object* v___f_1130_; lean_object* v___f_1131_; lean_object* v___f_1132_; lean_object* v___x_1133_; 
v_toBind_1125_ = lean_ctor_get(v_inst_1120_, 1);
lean_inc(v_toBind_1125_);
lean_dec_ref(v_inst_1120_);
v_share1_1126_ = lean_ctor_get(v_inst_1119_, 0);
lean_inc(v_share1_1126_);
v_assertShared_1127_ = lean_ctor_get(v_inst_1119_, 1);
lean_inc(v_assertShared_1127_);
v_isDebugEnabled_1128_ = lean_ctor_get(v_inst_1119_, 2);
lean_inc(v_isDebugEnabled_1128_);
lean_dec_ref(v_inst_1119_);
v___x_1129_ = lean_box(v_bi_1122_);
lean_inc_ref(v_b_1124_);
lean_inc_ref(v_t_1123_);
v___f_1130_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkForallS___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1130_, 0, v_x_1121_);
lean_closure_set(v___f_1130_, 1, v_t_1123_);
lean_closure_set(v___f_1130_, 2, v_b_1124_);
lean_closure_set(v___f_1130_, 3, v___x_1129_);
lean_closure_set(v___f_1130_, 4, v_share1_1126_);
lean_inc_ref(v___f_1130_);
v___f_1131_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1131_, 0, v___f_1130_);
lean_inc(v_toBind_1125_);
v___f_1132_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_1132_, 0, v___f_1130_);
lean_closure_set(v___f_1132_, 1, v_assertShared_1127_);
lean_closure_set(v___f_1132_, 2, v_b_1124_);
lean_closure_set(v___f_1132_, 3, v_toBind_1125_);
lean_closure_set(v___f_1132_, 4, v___f_1131_);
lean_closure_set(v___f_1132_, 5, v_t_1123_);
v___x_1133_ = lean_apply_4(v_toBind_1125_, lean_box(0), lean_box(0), v_isDebugEnabled_1128_, v___f_1132_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___redArg___boxed(lean_object* v_inst_1134_, lean_object* v_inst_1135_, lean_object* v_x_1136_, lean_object* v_bi_1137_, lean_object* v_t_1138_, lean_object* v_b_1139_){
_start:
{
uint8_t v_bi_boxed_1140_; lean_object* v_res_1141_; 
v_bi_boxed_1140_ = lean_unbox(v_bi_1137_);
v_res_1141_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v_inst_1134_, v_inst_1135_, v_x_1136_, v_bi_boxed_1140_, v_t_1138_, v_b_1139_);
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS(lean_object* v_m_1142_, lean_object* v_inst_1143_, lean_object* v_inst_1144_, lean_object* v_x_1145_, uint8_t v_bi_1146_, lean_object* v_t_1147_, lean_object* v_b_1148_){
_start:
{
lean_object* v___x_1149_; 
v___x_1149_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v_inst_1143_, v_inst_1144_, v_x_1145_, v_bi_1146_, v_t_1147_, v_b_1148_);
return v___x_1149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___boxed(lean_object* v_m_1150_, lean_object* v_inst_1151_, lean_object* v_inst_1152_, lean_object* v_x_1153_, lean_object* v_bi_1154_, lean_object* v_t_1155_, lean_object* v_b_1156_){
_start:
{
uint8_t v_bi_boxed_1157_; lean_object* v_res_1158_; 
v_bi_boxed_1157_ = lean_unbox(v_bi_1154_);
v_res_1158_ = l_Lean_Meta_Sym_Internal_mkForallS(v_m_1150_, v_inst_1151_, v_inst_1152_, v_x_1153_, v_bi_boxed_1157_, v_t_1155_, v_b_1156_);
return v_res_1158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__0(lean_object* v_x_1159_, lean_object* v_t_1160_, lean_object* v_v_1161_, lean_object* v_b_1162_, uint8_t v_nondep_1163_, lean_object* v_share1_1164_, lean_object* v_____r_1165_){
_start:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1166_ = l_Lean_Expr_letE___override(v_x_1159_, v_t_1160_, v_v_1161_, v_b_1162_, v_nondep_1163_);
v___x_1167_ = lean_apply_1(v_share1_1164_, v___x_1166_);
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__0___boxed(lean_object* v_x_1168_, lean_object* v_t_1169_, lean_object* v_v_1170_, lean_object* v_b_1171_, lean_object* v_nondep_1172_, lean_object* v_share1_1173_, lean_object* v_____r_1174_){
_start:
{
uint8_t v_nondep_boxed_1175_; lean_object* v_res_1176_; 
v_nondep_boxed_1175_ = lean_unbox(v_nondep_1172_);
v_res_1176_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__0(v_x_1168_, v_t_1169_, v_v_1170_, v_b_1171_, v_nondep_boxed_1175_, v_share1_1173_, v_____r_1174_);
return v_res_1176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__3(lean_object* v_assertShared_1177_, lean_object* v_v_1178_, lean_object* v_toBind_1179_, lean_object* v___f_1180_, lean_object* v_____r_1181_){
_start:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1182_ = lean_apply_1(v_assertShared_1177_, v_v_1178_);
v___x_1183_ = lean_apply_4(v_toBind_1179_, lean_box(0), lean_box(0), v___x_1182_, v___f_1180_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1(lean_object* v___f_1184_, lean_object* v_assertShared_1185_, lean_object* v_b_1186_, lean_object* v_toBind_1187_, lean_object* v___f_1188_, lean_object* v_v_1189_, lean_object* v_t_1190_, uint8_t v_____do__lift_1191_){
_start:
{
if (v_____do__lift_1191_ == 0)
{
lean_object* v___x_1192_; lean_object* v___x_1193_; 
lean_dec_ref(v_t_1190_);
lean_dec_ref(v_v_1189_);
lean_dec(v___f_1188_);
lean_dec(v_toBind_1187_);
lean_dec_ref(v_b_1186_);
lean_dec(v_assertShared_1185_);
v___x_1192_ = lean_box(0);
v___x_1193_ = lean_apply_1(v___f_1184_, v___x_1192_);
return v___x_1193_;
}
else
{
lean_object* v___f_1194_; lean_object* v___f_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
lean_dec(v___f_1184_);
lean_inc(v_toBind_1187_);
lean_inc(v_assertShared_1185_);
v___f_1194_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__2), 5, 4);
lean_closure_set(v___f_1194_, 0, v_assertShared_1185_);
lean_closure_set(v___f_1194_, 1, v_b_1186_);
lean_closure_set(v___f_1194_, 2, v_toBind_1187_);
lean_closure_set(v___f_1194_, 3, v___f_1188_);
lean_inc(v_toBind_1187_);
lean_inc(v_assertShared_1185_);
v___f_1195_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__3), 5, 4);
lean_closure_set(v___f_1195_, 0, v_assertShared_1185_);
lean_closure_set(v___f_1195_, 1, v_v_1189_);
lean_closure_set(v___f_1195_, 2, v_toBind_1187_);
lean_closure_set(v___f_1195_, 3, v___f_1194_);
v___x_1196_ = lean_apply_1(v_assertShared_1185_, v_t_1190_);
v___x_1197_ = lean_apply_4(v_toBind_1187_, lean_box(0), lean_box(0), v___x_1196_, v___f_1195_);
return v___x_1197_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1___boxed(lean_object* v___f_1198_, lean_object* v_assertShared_1199_, lean_object* v_b_1200_, lean_object* v_toBind_1201_, lean_object* v___f_1202_, lean_object* v_v_1203_, lean_object* v_t_1204_, lean_object* v_____do__lift_1205_){
_start:
{
uint8_t v_____do__lift_122__boxed_1206_; lean_object* v_res_1207_; 
v_____do__lift_122__boxed_1206_ = lean_unbox(v_____do__lift_1205_);
v_res_1207_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1(v___f_1198_, v_assertShared_1199_, v_b_1200_, v_toBind_1201_, v___f_1202_, v_v_1203_, v_t_1204_, v_____do__lift_122__boxed_1206_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg(lean_object* v_inst_1208_, lean_object* v_inst_1209_, lean_object* v_x_1210_, lean_object* v_t_1211_, lean_object* v_v_1212_, lean_object* v_b_1213_, uint8_t v_nondep_1214_){
_start:
{
lean_object* v_toBind_1215_; lean_object* v_share1_1216_; lean_object* v_assertShared_1217_; lean_object* v_isDebugEnabled_1218_; lean_object* v___x_1219_; lean_object* v___f_1220_; lean_object* v___f_1221_; lean_object* v___f_1222_; lean_object* v___x_1223_; 
v_toBind_1215_ = lean_ctor_get(v_inst_1209_, 1);
lean_inc(v_toBind_1215_);
lean_dec_ref(v_inst_1209_);
v_share1_1216_ = lean_ctor_get(v_inst_1208_, 0);
lean_inc(v_share1_1216_);
v_assertShared_1217_ = lean_ctor_get(v_inst_1208_, 1);
lean_inc(v_assertShared_1217_);
v_isDebugEnabled_1218_ = lean_ctor_get(v_inst_1208_, 2);
lean_inc(v_isDebugEnabled_1218_);
lean_dec_ref(v_inst_1208_);
v___x_1219_ = lean_box(v_nondep_1214_);
lean_inc_ref(v_b_1213_);
lean_inc_ref(v_v_1212_);
lean_inc_ref(v_t_1211_);
v___f_1220_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_1220_, 0, v_x_1210_);
lean_closure_set(v___f_1220_, 1, v_t_1211_);
lean_closure_set(v___f_1220_, 2, v_v_1212_);
lean_closure_set(v___f_1220_, 3, v_b_1213_);
lean_closure_set(v___f_1220_, 4, v___x_1219_);
lean_closure_set(v___f_1220_, 5, v_share1_1216_);
lean_inc_ref(v___f_1220_);
v___f_1221_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1221_, 0, v___f_1220_);
lean_inc(v_toBind_1215_);
v___f_1222_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_1222_, 0, v___f_1220_);
lean_closure_set(v___f_1222_, 1, v_assertShared_1217_);
lean_closure_set(v___f_1222_, 2, v_b_1213_);
lean_closure_set(v___f_1222_, 3, v_toBind_1215_);
lean_closure_set(v___f_1222_, 4, v___f_1221_);
lean_closure_set(v___f_1222_, 5, v_v_1212_);
lean_closure_set(v___f_1222_, 6, v_t_1211_);
v___x_1223_ = lean_apply_4(v_toBind_1215_, lean_box(0), lean_box(0), v_isDebugEnabled_1218_, v___f_1222_);
return v___x_1223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___boxed(lean_object* v_inst_1224_, lean_object* v_inst_1225_, lean_object* v_x_1226_, lean_object* v_t_1227_, lean_object* v_v_1228_, lean_object* v_b_1229_, lean_object* v_nondep_1230_){
_start:
{
uint8_t v_nondep_boxed_1231_; lean_object* v_res_1232_; 
v_nondep_boxed_1231_ = lean_unbox(v_nondep_1230_);
v_res_1232_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1224_, v_inst_1225_, v_x_1226_, v_t_1227_, v_v_1228_, v_b_1229_, v_nondep_boxed_1231_);
return v_res_1232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS(lean_object* v_m_1233_, lean_object* v_inst_1234_, lean_object* v_inst_1235_, lean_object* v_x_1236_, lean_object* v_t_1237_, lean_object* v_v_1238_, lean_object* v_b_1239_, uint8_t v_nondep_1240_){
_start:
{
lean_object* v___x_1241_; 
v___x_1241_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1234_, v_inst_1235_, v_x_1236_, v_t_1237_, v_v_1238_, v_b_1239_, v_nondep_1240_);
return v___x_1241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___boxed(lean_object* v_m_1242_, lean_object* v_inst_1243_, lean_object* v_inst_1244_, lean_object* v_x_1245_, lean_object* v_t_1246_, lean_object* v_v_1247_, lean_object* v_b_1248_, lean_object* v_nondep_1249_){
_start:
{
uint8_t v_nondep_boxed_1250_; lean_object* v_res_1251_; 
v_nondep_boxed_1250_ = lean_unbox(v_nondep_1249_);
v_res_1251_ = l_Lean_Meta_Sym_Internal_mkLetS(v_m_1242_, v_inst_1243_, v_inst_1244_, v_x_1245_, v_t_1246_, v_v_1247_, v_b_1248_, v_nondep_boxed_1250_);
return v_res_1251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkHaveS___redArg___lam__0(lean_object* v_x_1252_, lean_object* v_t_1253_, lean_object* v_v_1254_, lean_object* v_b_1255_, lean_object* v_share1_1256_, lean_object* v_____r_1257_){
_start:
{
uint8_t v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1258_ = 1;
v___x_1259_ = l_Lean_Expr_letE___override(v_x_1252_, v_t_1253_, v_v_1254_, v_b_1255_, v___x_1258_);
v___x_1260_ = lean_apply_1(v_share1_1256_, v___x_1259_);
return v___x_1260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkHaveS___redArg(lean_object* v_inst_1261_, lean_object* v_inst_1262_, lean_object* v_x_1263_, lean_object* v_t_1264_, lean_object* v_v_1265_, lean_object* v_b_1266_){
_start:
{
lean_object* v_toBind_1267_; lean_object* v_share1_1268_; lean_object* v_assertShared_1269_; lean_object* v_isDebugEnabled_1270_; lean_object* v___f_1271_; lean_object* v___f_1272_; lean_object* v___f_1273_; lean_object* v___x_1274_; 
v_toBind_1267_ = lean_ctor_get(v_inst_1262_, 1);
lean_inc(v_toBind_1267_);
lean_dec_ref(v_inst_1262_);
v_share1_1268_ = lean_ctor_get(v_inst_1261_, 0);
lean_inc(v_share1_1268_);
v_assertShared_1269_ = lean_ctor_get(v_inst_1261_, 1);
lean_inc(v_assertShared_1269_);
v_isDebugEnabled_1270_ = lean_ctor_get(v_inst_1261_, 2);
lean_inc(v_isDebugEnabled_1270_);
lean_dec_ref(v_inst_1261_);
lean_inc_ref(v_b_1266_);
lean_inc_ref(v_v_1265_);
lean_inc_ref(v_t_1264_);
v___f_1271_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkHaveS___redArg___lam__0), 6, 5);
lean_closure_set(v___f_1271_, 0, v_x_1263_);
lean_closure_set(v___f_1271_, 1, v_t_1264_);
lean_closure_set(v___f_1271_, 2, v_v_1265_);
lean_closure_set(v___f_1271_, 3, v_b_1266_);
lean_closure_set(v___f_1271_, 4, v_share1_1268_);
lean_inc_ref(v___f_1271_);
v___f_1272_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1272_, 0, v___f_1271_);
lean_inc(v_toBind_1267_);
v___f_1273_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_1273_, 0, v___f_1271_);
lean_closure_set(v___f_1273_, 1, v_assertShared_1269_);
lean_closure_set(v___f_1273_, 2, v_b_1266_);
lean_closure_set(v___f_1273_, 3, v_toBind_1267_);
lean_closure_set(v___f_1273_, 4, v___f_1272_);
lean_closure_set(v___f_1273_, 5, v_v_1265_);
lean_closure_set(v___f_1273_, 6, v_t_1264_);
v___x_1274_ = lean_apply_4(v_toBind_1267_, lean_box(0), lean_box(0), v_isDebugEnabled_1270_, v___f_1273_);
return v___x_1274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkHaveS(lean_object* v_m_1275_, lean_object* v_inst_1276_, lean_object* v_inst_1277_, lean_object* v_x_1278_, lean_object* v_t_1279_, lean_object* v_v_1280_, lean_object* v_b_1281_){
_start:
{
lean_object* v___x_1282_; 
v___x_1282_ = l_Lean_Meta_Sym_Internal_mkHaveS___redArg(v_inst_1276_, v_inst_1277_, v_x_1278_, v_t_1279_, v_v_1280_, v_b_1281_);
return v___x_1282_;
}
}
static lean_object* _init_l_Lean_Expr_updateAppS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1285_ = ((lean_object*)(l_Lean_Expr_updateAppS_x21___redArg___closed__1));
v___x_1286_ = lean_unsigned_to_nat(25u);
v___x_1287_ = lean_unsigned_to_nat(148u);
v___x_1288_ = ((lean_object*)(l_Lean_Expr_updateAppS_x21___redArg___closed__0));
v___x_1289_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1290_ = l_mkPanicMessageWithDecl(v___x_1289_, v___x_1288_, v___x_1287_, v___x_1286_, v___x_1285_);
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateAppS_x21___redArg(lean_object* v_inst_1291_, lean_object* v_inst_1292_, lean_object* v_e_1293_, lean_object* v_newFn_1294_, lean_object* v_newArg_1295_){
_start:
{
uint8_t v___y_1297_; 
if (lean_obj_tag(v_e_1293_) == 5)
{
lean_object* v_fn_1302_; lean_object* v_arg_1303_; uint8_t v___x_1304_; 
v_fn_1302_ = lean_ctor_get(v_e_1293_, 0);
v_arg_1303_ = lean_ctor_get(v_e_1293_, 1);
v___x_1304_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fn_1302_, v_newFn_1294_);
if (v___x_1304_ == 0)
{
v___y_1297_ = v___x_1304_;
goto v___jp_1296_;
}
else
{
uint8_t v___x_1305_; 
v___x_1305_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_1303_, v_newArg_1295_);
v___y_1297_ = v___x_1305_;
goto v___jp_1296_;
}
}
else
{
lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
lean_dec_ref(v_newArg_1295_);
lean_dec_ref(v_newFn_1294_);
lean_dec_ref(v_e_1293_);
lean_dec_ref(v_inst_1291_);
v___x_1306_ = l_Lean_instInhabitedExpr;
v___x_1307_ = l_instInhabitedOfMonad___redArg(v_inst_1292_, v___x_1306_);
v___x_1308_ = lean_obj_once(&l_Lean_Expr_updateAppS_x21___redArg___closed__2, &l_Lean_Expr_updateAppS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateAppS_x21___redArg___closed__2);
v___x_1309_ = l_panic___redArg(v___x_1307_, v___x_1308_);
return v___x_1309_;
}
v___jp_1296_:
{
if (v___y_1297_ == 0)
{
lean_object* v___x_1298_; 
lean_dec_ref(v_e_1293_);
v___x_1298_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1291_, v_inst_1292_, v_newFn_1294_, v_newArg_1295_);
return v___x_1298_;
}
else
{
lean_object* v_toApplicative_1299_; lean_object* v_toPure_1300_; lean_object* v___x_1301_; 
lean_dec_ref(v_newArg_1295_);
lean_dec_ref(v_newFn_1294_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateAppS_x21(lean_object* v_m_1310_, lean_object* v_inst_1311_, lean_object* v_inst_1312_, lean_object* v_e_1313_, lean_object* v_newFn_1314_, lean_object* v_newArg_1315_){
_start:
{
uint8_t v___y_1317_; 
if (lean_obj_tag(v_e_1313_) == 5)
{
lean_object* v_fn_1322_; lean_object* v_arg_1323_; uint8_t v___x_1324_; 
v_fn_1322_ = lean_ctor_get(v_e_1313_, 0);
v_arg_1323_ = lean_ctor_get(v_e_1313_, 1);
v___x_1324_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fn_1322_, v_newFn_1314_);
if (v___x_1324_ == 0)
{
v___y_1317_ = v___x_1324_;
goto v___jp_1316_;
}
else
{
uint8_t v___x_1325_; 
v___x_1325_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_1323_, v_newArg_1315_);
v___y_1317_ = v___x_1325_;
goto v___jp_1316_;
}
}
else
{
lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; 
lean_dec_ref(v_newArg_1315_);
lean_dec_ref(v_newFn_1314_);
lean_dec_ref(v_e_1313_);
lean_dec_ref(v_inst_1311_);
v___x_1326_ = l_Lean_instInhabitedExpr;
v___x_1327_ = l_instInhabitedOfMonad___redArg(v_inst_1312_, v___x_1326_);
v___x_1328_ = lean_obj_once(&l_Lean_Expr_updateAppS_x21___redArg___closed__2, &l_Lean_Expr_updateAppS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateAppS_x21___redArg___closed__2);
v___x_1329_ = l_panic___redArg(v___x_1327_, v___x_1328_);
return v___x_1329_;
}
v___jp_1316_:
{
if (v___y_1317_ == 0)
{
lean_object* v___x_1318_; 
lean_dec_ref(v_e_1313_);
v___x_1318_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1311_, v_inst_1312_, v_newFn_1314_, v_newArg_1315_);
return v___x_1318_;
}
else
{
lean_object* v_toApplicative_1319_; lean_object* v_toPure_1320_; lean_object* v___x_1321_; 
lean_dec_ref(v_newArg_1315_);
lean_dec_ref(v_newFn_1314_);
lean_dec_ref(v_inst_1311_);
v_toApplicative_1319_ = lean_ctor_get(v_inst_1312_, 0);
lean_inc_ref(v_toApplicative_1319_);
lean_dec_ref(v_inst_1312_);
v_toPure_1320_ = lean_ctor_get(v_toApplicative_1319_, 1);
lean_inc(v_toPure_1320_);
lean_dec_ref(v_toApplicative_1319_);
v___x_1321_ = lean_apply_2(v_toPure_1320_, lean_box(0), v_e_1313_);
return v___x_1321_;
}
}
}
}
static lean_object* _init_l_Lean_Expr_updateMDataS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; 
v___x_1332_ = ((lean_object*)(l_Lean_Expr_updateMDataS_x21___redArg___closed__1));
v___x_1333_ = lean_unsigned_to_nat(24u);
v___x_1334_ = lean_unsigned_to_nat(152u);
v___x_1335_ = ((lean_object*)(l_Lean_Expr_updateMDataS_x21___redArg___closed__0));
v___x_1336_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1337_ = l_mkPanicMessageWithDecl(v___x_1336_, v___x_1335_, v___x_1334_, v___x_1333_, v___x_1332_);
return v___x_1337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateMDataS_x21___redArg(lean_object* v_inst_1338_, lean_object* v_inst_1339_, lean_object* v_e_1340_, lean_object* v_newExpr_1341_){
_start:
{
if (lean_obj_tag(v_e_1340_) == 10)
{
lean_object* v_data_1342_; lean_object* v_expr_1343_; uint8_t v___x_1344_; 
v_data_1342_ = lean_ctor_get(v_e_1340_, 0);
v_expr_1343_ = lean_ctor_get(v_e_1340_, 1);
v___x_1344_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_expr_1343_, v_newExpr_1341_);
if (v___x_1344_ == 0)
{
lean_object* v___x_1345_; 
lean_inc(v_data_1342_);
lean_dec_ref(v_e_1340_);
v___x_1345_ = l_Lean_Meta_Sym_Internal_mkMDataS___redArg(v_inst_1338_, v_inst_1339_, v_data_1342_, v_newExpr_1341_);
return v___x_1345_;
}
else
{
lean_object* v_toApplicative_1346_; lean_object* v_toPure_1347_; lean_object* v___x_1348_; 
lean_dec_ref(v_newExpr_1341_);
lean_dec_ref(v_inst_1338_);
v_toApplicative_1346_ = lean_ctor_get(v_inst_1339_, 0);
lean_inc_ref(v_toApplicative_1346_);
lean_dec_ref(v_inst_1339_);
v_toPure_1347_ = lean_ctor_get(v_toApplicative_1346_, 1);
lean_inc(v_toPure_1347_);
lean_dec_ref(v_toApplicative_1346_);
v___x_1348_ = lean_apply_2(v_toPure_1347_, lean_box(0), v_e_1340_);
return v___x_1348_;
}
}
else
{
lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; 
lean_dec_ref(v_newExpr_1341_);
lean_dec_ref(v_e_1340_);
lean_dec_ref(v_inst_1338_);
v___x_1349_ = l_Lean_instInhabitedExpr;
v___x_1350_ = l_instInhabitedOfMonad___redArg(v_inst_1339_, v___x_1349_);
v___x_1351_ = lean_obj_once(&l_Lean_Expr_updateMDataS_x21___redArg___closed__2, &l_Lean_Expr_updateMDataS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateMDataS_x21___redArg___closed__2);
v___x_1352_ = l_panic___redArg(v___x_1350_, v___x_1351_);
return v___x_1352_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateMDataS_x21(lean_object* v_m_1353_, lean_object* v_inst_1354_, lean_object* v_inst_1355_, lean_object* v_e_1356_, lean_object* v_newExpr_1357_){
_start:
{
if (lean_obj_tag(v_e_1356_) == 10)
{
lean_object* v_data_1358_; lean_object* v_expr_1359_; uint8_t v___x_1360_; 
v_data_1358_ = lean_ctor_get(v_e_1356_, 0);
v_expr_1359_ = lean_ctor_get(v_e_1356_, 1);
v___x_1360_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_expr_1359_, v_newExpr_1357_);
if (v___x_1360_ == 0)
{
lean_object* v___x_1361_; 
lean_inc(v_data_1358_);
lean_dec_ref(v_e_1356_);
v___x_1361_ = l_Lean_Meta_Sym_Internal_mkMDataS___redArg(v_inst_1354_, v_inst_1355_, v_data_1358_, v_newExpr_1357_);
return v___x_1361_;
}
else
{
lean_object* v_toApplicative_1362_; lean_object* v_toPure_1363_; lean_object* v___x_1364_; 
lean_dec_ref(v_newExpr_1357_);
lean_dec_ref(v_inst_1354_);
v_toApplicative_1362_ = lean_ctor_get(v_inst_1355_, 0);
lean_inc_ref(v_toApplicative_1362_);
lean_dec_ref(v_inst_1355_);
v_toPure_1363_ = lean_ctor_get(v_toApplicative_1362_, 1);
lean_inc(v_toPure_1363_);
lean_dec_ref(v_toApplicative_1362_);
v___x_1364_ = lean_apply_2(v_toPure_1363_, lean_box(0), v_e_1356_);
return v___x_1364_;
}
}
else
{
lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; 
lean_dec_ref(v_newExpr_1357_);
lean_dec_ref(v_e_1356_);
lean_dec_ref(v_inst_1354_);
v___x_1365_ = l_Lean_instInhabitedExpr;
v___x_1366_ = l_instInhabitedOfMonad___redArg(v_inst_1355_, v___x_1365_);
v___x_1367_ = lean_obj_once(&l_Lean_Expr_updateMDataS_x21___redArg___closed__2, &l_Lean_Expr_updateMDataS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateMDataS_x21___redArg___closed__2);
v___x_1368_ = l_panic___redArg(v___x_1366_, v___x_1367_);
return v___x_1368_;
}
}
}
static lean_object* _init_l_Lean_Expr_updateProjS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; 
v___x_1371_ = ((lean_object*)(l_Lean_Expr_updateProjS_x21___redArg___closed__1));
v___x_1372_ = lean_unsigned_to_nat(25u);
v___x_1373_ = lean_unsigned_to_nat(156u);
v___x_1374_ = ((lean_object*)(l_Lean_Expr_updateProjS_x21___redArg___closed__0));
v___x_1375_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1376_ = l_mkPanicMessageWithDecl(v___x_1375_, v___x_1374_, v___x_1373_, v___x_1372_, v___x_1371_);
return v___x_1376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateProjS_x21___redArg(lean_object* v_inst_1377_, lean_object* v_inst_1378_, lean_object* v_e_1379_, lean_object* v_newExpr_1380_){
_start:
{
if (lean_obj_tag(v_e_1379_) == 11)
{
lean_object* v_typeName_1381_; lean_object* v_idx_1382_; lean_object* v_struct_1383_; uint8_t v___x_1384_; 
v_typeName_1381_ = lean_ctor_get(v_e_1379_, 0);
v_idx_1382_ = lean_ctor_get(v_e_1379_, 1);
v_struct_1383_ = lean_ctor_get(v_e_1379_, 2);
v___x_1384_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_1383_, v_newExpr_1380_);
if (v___x_1384_ == 0)
{
lean_object* v___x_1385_; 
lean_inc(v_idx_1382_);
lean_inc(v_typeName_1381_);
lean_dec_ref(v_e_1379_);
v___x_1385_ = l_Lean_Meta_Sym_Internal_mkProjS___redArg(v_inst_1377_, v_inst_1378_, v_typeName_1381_, v_idx_1382_, v_newExpr_1380_);
return v___x_1385_;
}
else
{
lean_object* v_toApplicative_1386_; lean_object* v_toPure_1387_; lean_object* v___x_1388_; 
lean_dec_ref(v_newExpr_1380_);
lean_dec_ref(v_inst_1377_);
v_toApplicative_1386_ = lean_ctor_get(v_inst_1378_, 0);
lean_inc_ref(v_toApplicative_1386_);
lean_dec_ref(v_inst_1378_);
v_toPure_1387_ = lean_ctor_get(v_toApplicative_1386_, 1);
lean_inc(v_toPure_1387_);
lean_dec_ref(v_toApplicative_1386_);
v___x_1388_ = lean_apply_2(v_toPure_1387_, lean_box(0), v_e_1379_);
return v___x_1388_;
}
}
else
{
lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; 
lean_dec_ref(v_newExpr_1380_);
lean_dec_ref(v_e_1379_);
lean_dec_ref(v_inst_1377_);
v___x_1389_ = l_Lean_instInhabitedExpr;
v___x_1390_ = l_instInhabitedOfMonad___redArg(v_inst_1378_, v___x_1389_);
v___x_1391_ = lean_obj_once(&l_Lean_Expr_updateProjS_x21___redArg___closed__2, &l_Lean_Expr_updateProjS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateProjS_x21___redArg___closed__2);
v___x_1392_ = l_panic___redArg(v___x_1390_, v___x_1391_);
return v___x_1392_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateProjS_x21(lean_object* v_m_1393_, lean_object* v_inst_1394_, lean_object* v_inst_1395_, lean_object* v_e_1396_, lean_object* v_newExpr_1397_){
_start:
{
if (lean_obj_tag(v_e_1396_) == 11)
{
lean_object* v_typeName_1398_; lean_object* v_idx_1399_; lean_object* v_struct_1400_; uint8_t v___x_1401_; 
v_typeName_1398_ = lean_ctor_get(v_e_1396_, 0);
v_idx_1399_ = lean_ctor_get(v_e_1396_, 1);
v_struct_1400_ = lean_ctor_get(v_e_1396_, 2);
v___x_1401_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_1400_, v_newExpr_1397_);
if (v___x_1401_ == 0)
{
lean_object* v___x_1402_; 
lean_inc(v_idx_1399_);
lean_inc(v_typeName_1398_);
lean_dec_ref(v_e_1396_);
v___x_1402_ = l_Lean_Meta_Sym_Internal_mkProjS___redArg(v_inst_1394_, v_inst_1395_, v_typeName_1398_, v_idx_1399_, v_newExpr_1397_);
return v___x_1402_;
}
else
{
lean_object* v_toApplicative_1403_; lean_object* v_toPure_1404_; lean_object* v___x_1405_; 
lean_dec_ref(v_newExpr_1397_);
lean_dec_ref(v_inst_1394_);
v_toApplicative_1403_ = lean_ctor_get(v_inst_1395_, 0);
lean_inc_ref(v_toApplicative_1403_);
lean_dec_ref(v_inst_1395_);
v_toPure_1404_ = lean_ctor_get(v_toApplicative_1403_, 1);
lean_inc(v_toPure_1404_);
lean_dec_ref(v_toApplicative_1403_);
v___x_1405_ = lean_apply_2(v_toPure_1404_, lean_box(0), v_e_1396_);
return v___x_1405_;
}
}
else
{
lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; 
lean_dec_ref(v_newExpr_1397_);
lean_dec_ref(v_e_1396_);
lean_dec_ref(v_inst_1394_);
v___x_1406_ = l_Lean_instInhabitedExpr;
v___x_1407_ = l_instInhabitedOfMonad___redArg(v_inst_1395_, v___x_1406_);
v___x_1408_ = lean_obj_once(&l_Lean_Expr_updateProjS_x21___redArg___closed__2, &l_Lean_Expr_updateProjS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateProjS_x21___redArg___closed__2);
v___x_1409_ = l_panic___redArg(v___x_1407_, v___x_1408_);
return v___x_1409_;
}
}
}
static lean_object* _init_l_Lean_Expr_updateForallS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; 
v___x_1412_ = ((lean_object*)(l_Lean_Expr_updateForallS_x21___redArg___closed__1));
v___x_1413_ = lean_unsigned_to_nat(31u);
v___x_1414_ = lean_unsigned_to_nat(160u);
v___x_1415_ = ((lean_object*)(l_Lean_Expr_updateForallS_x21___redArg___closed__0));
v___x_1416_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1417_ = l_mkPanicMessageWithDecl(v___x_1416_, v___x_1415_, v___x_1414_, v___x_1413_, v___x_1412_);
return v___x_1417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallS_x21___redArg(lean_object* v_inst_1418_, lean_object* v_inst_1419_, lean_object* v_e_1420_, lean_object* v_newDomain_1421_, lean_object* v_newBody_1422_){
_start:
{
if (lean_obj_tag(v_e_1420_) == 7)
{
lean_object* v_binderName_1423_; lean_object* v_binderType_1424_; lean_object* v_body_1425_; uint8_t v_binderInfo_1426_; uint8_t v___y_1428_; uint8_t v___x_1433_; 
v_binderName_1423_ = lean_ctor_get(v_e_1420_, 0);
v_binderType_1424_ = lean_ctor_get(v_e_1420_, 1);
v_body_1425_ = lean_ctor_get(v_e_1420_, 2);
v_binderInfo_1426_ = lean_ctor_get_uint8(v_e_1420_, sizeof(void*)*3 + 8);
v___x_1433_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_1424_, v_newDomain_1421_);
if (v___x_1433_ == 0)
{
v___y_1428_ = v___x_1433_;
goto v___jp_1427_;
}
else
{
uint8_t v___x_1434_; 
v___x_1434_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1425_, v_newBody_1422_);
v___y_1428_ = v___x_1434_;
goto v___jp_1427_;
}
v___jp_1427_:
{
if (v___y_1428_ == 0)
{
lean_object* v___x_1429_; 
lean_inc(v_binderName_1423_);
lean_dec_ref(v_e_1420_);
v___x_1429_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v_inst_1418_, v_inst_1419_, v_binderName_1423_, v_binderInfo_1426_, v_newDomain_1421_, v_newBody_1422_);
return v___x_1429_;
}
else
{
lean_object* v_toApplicative_1430_; lean_object* v_toPure_1431_; lean_object* v___x_1432_; 
lean_dec_ref(v_newBody_1422_);
lean_dec_ref(v_newDomain_1421_);
lean_dec_ref(v_inst_1418_);
v_toApplicative_1430_ = lean_ctor_get(v_inst_1419_, 0);
lean_inc_ref(v_toApplicative_1430_);
lean_dec_ref(v_inst_1419_);
v_toPure_1431_ = lean_ctor_get(v_toApplicative_1430_, 1);
lean_inc(v_toPure_1431_);
lean_dec_ref(v_toApplicative_1430_);
v___x_1432_ = lean_apply_2(v_toPure_1431_, lean_box(0), v_e_1420_);
return v___x_1432_;
}
}
}
else
{
lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; 
lean_dec_ref(v_newBody_1422_);
lean_dec_ref(v_newDomain_1421_);
lean_dec_ref(v_e_1420_);
lean_dec_ref(v_inst_1418_);
v___x_1435_ = l_Lean_instInhabitedExpr;
v___x_1436_ = l_instInhabitedOfMonad___redArg(v_inst_1419_, v___x_1435_);
v___x_1437_ = lean_obj_once(&l_Lean_Expr_updateForallS_x21___redArg___closed__2, &l_Lean_Expr_updateForallS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateForallS_x21___redArg___closed__2);
v___x_1438_ = l_panic___redArg(v___x_1436_, v___x_1437_);
return v___x_1438_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallS_x21(lean_object* v_m_1439_, lean_object* v_inst_1440_, lean_object* v_inst_1441_, lean_object* v_e_1442_, lean_object* v_newDomain_1443_, lean_object* v_newBody_1444_){
_start:
{
if (lean_obj_tag(v_e_1442_) == 7)
{
lean_object* v_binderName_1445_; lean_object* v_binderType_1446_; lean_object* v_body_1447_; uint8_t v_binderInfo_1448_; uint8_t v___y_1450_; uint8_t v___x_1455_; 
v_binderName_1445_ = lean_ctor_get(v_e_1442_, 0);
v_binderType_1446_ = lean_ctor_get(v_e_1442_, 1);
v_body_1447_ = lean_ctor_get(v_e_1442_, 2);
v_binderInfo_1448_ = lean_ctor_get_uint8(v_e_1442_, sizeof(void*)*3 + 8);
v___x_1455_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_1446_, v_newDomain_1443_);
if (v___x_1455_ == 0)
{
v___y_1450_ = v___x_1455_;
goto v___jp_1449_;
}
else
{
uint8_t v___x_1456_; 
v___x_1456_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1447_, v_newBody_1444_);
v___y_1450_ = v___x_1456_;
goto v___jp_1449_;
}
v___jp_1449_:
{
if (v___y_1450_ == 0)
{
lean_object* v___x_1451_; 
lean_inc(v_binderName_1445_);
lean_dec_ref(v_e_1442_);
v___x_1451_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v_inst_1440_, v_inst_1441_, v_binderName_1445_, v_binderInfo_1448_, v_newDomain_1443_, v_newBody_1444_);
return v___x_1451_;
}
else
{
lean_object* v_toApplicative_1452_; lean_object* v_toPure_1453_; lean_object* v___x_1454_; 
lean_dec_ref(v_newBody_1444_);
lean_dec_ref(v_newDomain_1443_);
lean_dec_ref(v_inst_1440_);
v_toApplicative_1452_ = lean_ctor_get(v_inst_1441_, 0);
lean_inc_ref(v_toApplicative_1452_);
lean_dec_ref(v_inst_1441_);
v_toPure_1453_ = lean_ctor_get(v_toApplicative_1452_, 1);
lean_inc(v_toPure_1453_);
lean_dec_ref(v_toApplicative_1452_);
v___x_1454_ = lean_apply_2(v_toPure_1453_, lean_box(0), v_e_1442_);
return v___x_1454_;
}
}
}
else
{
lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; 
lean_dec_ref(v_newBody_1444_);
lean_dec_ref(v_newDomain_1443_);
lean_dec_ref(v_e_1442_);
lean_dec_ref(v_inst_1440_);
v___x_1457_ = l_Lean_instInhabitedExpr;
v___x_1458_ = l_instInhabitedOfMonad___redArg(v_inst_1441_, v___x_1457_);
v___x_1459_ = lean_obj_once(&l_Lean_Expr_updateForallS_x21___redArg___closed__2, &l_Lean_Expr_updateForallS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateForallS_x21___redArg___closed__2);
v___x_1460_ = l_panic___redArg(v___x_1458_, v___x_1459_);
return v___x_1460_;
}
}
}
static lean_object* _init_l_Lean_Expr_updateLambdaS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; 
v___x_1463_ = ((lean_object*)(l_Lean_Expr_updateLambdaS_x21___redArg___closed__1));
v___x_1464_ = lean_unsigned_to_nat(27u);
v___x_1465_ = lean_unsigned_to_nat(167u);
v___x_1466_ = ((lean_object*)(l_Lean_Expr_updateLambdaS_x21___redArg___closed__0));
v___x_1467_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1468_ = l_mkPanicMessageWithDecl(v___x_1467_, v___x_1466_, v___x_1465_, v___x_1464_, v___x_1463_);
return v___x_1468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLambdaS_x21___redArg(lean_object* v_inst_1469_, lean_object* v_inst_1470_, lean_object* v_e_1471_, lean_object* v_newDomain_1472_, lean_object* v_newBody_1473_){
_start:
{
if (lean_obj_tag(v_e_1471_) == 6)
{
lean_object* v_binderName_1474_; lean_object* v_binderType_1475_; lean_object* v_body_1476_; uint8_t v_binderInfo_1477_; uint8_t v___y_1479_; uint8_t v___x_1484_; 
v_binderName_1474_ = lean_ctor_get(v_e_1471_, 0);
v_binderType_1475_ = lean_ctor_get(v_e_1471_, 1);
v_body_1476_ = lean_ctor_get(v_e_1471_, 2);
v_binderInfo_1477_ = lean_ctor_get_uint8(v_e_1471_, sizeof(void*)*3 + 8);
v___x_1484_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_1475_, v_newDomain_1472_);
if (v___x_1484_ == 0)
{
v___y_1479_ = v___x_1484_;
goto v___jp_1478_;
}
else
{
uint8_t v___x_1485_; 
v___x_1485_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1476_, v_newBody_1473_);
v___y_1479_ = v___x_1485_;
goto v___jp_1478_;
}
v___jp_1478_:
{
if (v___y_1479_ == 0)
{
lean_object* v___x_1480_; 
lean_inc(v_binderName_1474_);
lean_dec_ref(v_e_1471_);
v___x_1480_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v_inst_1469_, v_inst_1470_, v_binderName_1474_, v_binderInfo_1477_, v_newDomain_1472_, v_newBody_1473_);
return v___x_1480_;
}
else
{
lean_object* v_toApplicative_1481_; lean_object* v_toPure_1482_; lean_object* v___x_1483_; 
lean_dec_ref(v_newBody_1473_);
lean_dec_ref(v_newDomain_1472_);
lean_dec_ref(v_inst_1469_);
v_toApplicative_1481_ = lean_ctor_get(v_inst_1470_, 0);
lean_inc_ref(v_toApplicative_1481_);
lean_dec_ref(v_inst_1470_);
v_toPure_1482_ = lean_ctor_get(v_toApplicative_1481_, 1);
lean_inc(v_toPure_1482_);
lean_dec_ref(v_toApplicative_1481_);
v___x_1483_ = lean_apply_2(v_toPure_1482_, lean_box(0), v_e_1471_);
return v___x_1483_;
}
}
}
else
{
lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; 
lean_dec_ref(v_newBody_1473_);
lean_dec_ref(v_newDomain_1472_);
lean_dec_ref(v_e_1471_);
lean_dec_ref(v_inst_1469_);
v___x_1486_ = l_Lean_instInhabitedExpr;
v___x_1487_ = l_instInhabitedOfMonad___redArg(v_inst_1470_, v___x_1486_);
v___x_1488_ = lean_obj_once(&l_Lean_Expr_updateLambdaS_x21___redArg___closed__2, &l_Lean_Expr_updateLambdaS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateLambdaS_x21___redArg___closed__2);
v___x_1489_ = l_panic___redArg(v___x_1487_, v___x_1488_);
return v___x_1489_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLambdaS_x21(lean_object* v_m_1490_, lean_object* v_inst_1491_, lean_object* v_inst_1492_, lean_object* v_e_1493_, lean_object* v_newDomain_1494_, lean_object* v_newBody_1495_){
_start:
{
if (lean_obj_tag(v_e_1493_) == 6)
{
lean_object* v_binderName_1496_; lean_object* v_binderType_1497_; lean_object* v_body_1498_; uint8_t v_binderInfo_1499_; uint8_t v___y_1501_; uint8_t v___x_1506_; 
v_binderName_1496_ = lean_ctor_get(v_e_1493_, 0);
v_binderType_1497_ = lean_ctor_get(v_e_1493_, 1);
v_body_1498_ = lean_ctor_get(v_e_1493_, 2);
v_binderInfo_1499_ = lean_ctor_get_uint8(v_e_1493_, sizeof(void*)*3 + 8);
v___x_1506_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_1497_, v_newDomain_1494_);
if (v___x_1506_ == 0)
{
v___y_1501_ = v___x_1506_;
goto v___jp_1500_;
}
else
{
uint8_t v___x_1507_; 
v___x_1507_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1498_, v_newBody_1495_);
v___y_1501_ = v___x_1507_;
goto v___jp_1500_;
}
v___jp_1500_:
{
if (v___y_1501_ == 0)
{
lean_object* v___x_1502_; 
lean_inc(v_binderName_1496_);
lean_dec_ref(v_e_1493_);
v___x_1502_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v_inst_1491_, v_inst_1492_, v_binderName_1496_, v_binderInfo_1499_, v_newDomain_1494_, v_newBody_1495_);
return v___x_1502_;
}
else
{
lean_object* v_toApplicative_1503_; lean_object* v_toPure_1504_; lean_object* v___x_1505_; 
lean_dec_ref(v_newBody_1495_);
lean_dec_ref(v_newDomain_1494_);
lean_dec_ref(v_inst_1491_);
v_toApplicative_1503_ = lean_ctor_get(v_inst_1492_, 0);
lean_inc_ref(v_toApplicative_1503_);
lean_dec_ref(v_inst_1492_);
v_toPure_1504_ = lean_ctor_get(v_toApplicative_1503_, 1);
lean_inc(v_toPure_1504_);
lean_dec_ref(v_toApplicative_1503_);
v___x_1505_ = lean_apply_2(v_toPure_1504_, lean_box(0), v_e_1493_);
return v___x_1505_;
}
}
}
else
{
lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; 
lean_dec_ref(v_newBody_1495_);
lean_dec_ref(v_newDomain_1494_);
lean_dec_ref(v_e_1493_);
lean_dec_ref(v_inst_1491_);
v___x_1508_ = l_Lean_instInhabitedExpr;
v___x_1509_ = l_instInhabitedOfMonad___redArg(v_inst_1492_, v___x_1508_);
v___x_1510_ = lean_obj_once(&l_Lean_Expr_updateLambdaS_x21___redArg___closed__2, &l_Lean_Expr_updateLambdaS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateLambdaS_x21___redArg___closed__2);
v___x_1511_ = l_panic___redArg(v___x_1509_, v___x_1510_);
return v___x_1511_;
}
}
}
static lean_object* _init_l_Lean_Expr_updateLetS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; 
v___x_1514_ = ((lean_object*)(l_Lean_Expr_updateLetS_x21___redArg___closed__1));
v___x_1515_ = lean_unsigned_to_nat(34u);
v___x_1516_ = lean_unsigned_to_nat(174u);
v___x_1517_ = ((lean_object*)(l_Lean_Expr_updateLetS_x21___redArg___closed__0));
v___x_1518_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1519_ = l_mkPanicMessageWithDecl(v___x_1518_, v___x_1517_, v___x_1516_, v___x_1515_, v___x_1514_);
return v___x_1519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLetS_x21___redArg(lean_object* v_inst_1520_, lean_object* v_inst_1521_, lean_object* v_e_1522_, lean_object* v_newType_1523_, lean_object* v_newVal_1524_, lean_object* v_newBody_1525_){
_start:
{
if (lean_obj_tag(v_e_1522_) == 8)
{
lean_object* v_declName_1526_; lean_object* v_type_1527_; lean_object* v_value_1528_; lean_object* v_body_1529_; uint8_t v_nondep_1530_; uint8_t v___y_1532_; uint8_t v___x_1539_; 
v_declName_1526_ = lean_ctor_get(v_e_1522_, 0);
v_type_1527_ = lean_ctor_get(v_e_1522_, 1);
v_value_1528_ = lean_ctor_get(v_e_1522_, 2);
v_body_1529_ = lean_ctor_get(v_e_1522_, 3);
v_nondep_1530_ = lean_ctor_get_uint8(v_e_1522_, sizeof(void*)*4 + 8);
v___x_1539_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_type_1527_, v_newType_1523_);
if (v___x_1539_ == 0)
{
v___y_1532_ = v___x_1539_;
goto v___jp_1531_;
}
else
{
uint8_t v___x_1540_; 
v___x_1540_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_value_1528_, v_newVal_1524_);
v___y_1532_ = v___x_1540_;
goto v___jp_1531_;
}
v___jp_1531_:
{
if (v___y_1532_ == 0)
{
lean_object* v___x_1533_; 
lean_inc(v_declName_1526_);
lean_dec_ref(v_e_1522_);
v___x_1533_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1520_, v_inst_1521_, v_declName_1526_, v_newType_1523_, v_newVal_1524_, v_newBody_1525_, v_nondep_1530_);
return v___x_1533_;
}
else
{
uint8_t v___x_1534_; 
v___x_1534_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1529_, v_newBody_1525_);
if (v___x_1534_ == 0)
{
lean_object* v___x_1535_; 
lean_inc(v_declName_1526_);
lean_dec_ref(v_e_1522_);
v___x_1535_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1520_, v_inst_1521_, v_declName_1526_, v_newType_1523_, v_newVal_1524_, v_newBody_1525_, v_nondep_1530_);
return v___x_1535_;
}
else
{
lean_object* v_toApplicative_1536_; lean_object* v_toPure_1537_; lean_object* v___x_1538_; 
lean_dec_ref(v_newBody_1525_);
lean_dec_ref(v_newVal_1524_);
lean_dec_ref(v_newType_1523_);
lean_dec_ref(v_inst_1520_);
v_toApplicative_1536_ = lean_ctor_get(v_inst_1521_, 0);
lean_inc_ref(v_toApplicative_1536_);
lean_dec_ref(v_inst_1521_);
v_toPure_1537_ = lean_ctor_get(v_toApplicative_1536_, 1);
lean_inc(v_toPure_1537_);
lean_dec_ref(v_toApplicative_1536_);
v___x_1538_ = lean_apply_2(v_toPure_1537_, lean_box(0), v_e_1522_);
return v___x_1538_;
}
}
}
}
else
{
lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; 
lean_dec_ref(v_newBody_1525_);
lean_dec_ref(v_newVal_1524_);
lean_dec_ref(v_newType_1523_);
lean_dec_ref(v_e_1522_);
lean_dec_ref(v_inst_1520_);
v___x_1541_ = l_Lean_instInhabitedExpr;
v___x_1542_ = l_instInhabitedOfMonad___redArg(v_inst_1521_, v___x_1541_);
v___x_1543_ = lean_obj_once(&l_Lean_Expr_updateLetS_x21___redArg___closed__2, &l_Lean_Expr_updateLetS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateLetS_x21___redArg___closed__2);
v___x_1544_ = l_panic___redArg(v___x_1542_, v___x_1543_);
return v___x_1544_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLetS_x21(lean_object* v_m_1545_, lean_object* v_inst_1546_, lean_object* v_inst_1547_, lean_object* v_e_1548_, lean_object* v_newType_1549_, lean_object* v_newVal_1550_, lean_object* v_newBody_1551_){
_start:
{
if (lean_obj_tag(v_e_1548_) == 8)
{
lean_object* v_declName_1552_; lean_object* v_type_1553_; lean_object* v_value_1554_; lean_object* v_body_1555_; uint8_t v_nondep_1556_; uint8_t v___y_1558_; uint8_t v___x_1565_; 
v_declName_1552_ = lean_ctor_get(v_e_1548_, 0);
v_type_1553_ = lean_ctor_get(v_e_1548_, 1);
v_value_1554_ = lean_ctor_get(v_e_1548_, 2);
v_body_1555_ = lean_ctor_get(v_e_1548_, 3);
v_nondep_1556_ = lean_ctor_get_uint8(v_e_1548_, sizeof(void*)*4 + 8);
v___x_1565_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_type_1553_, v_newType_1549_);
if (v___x_1565_ == 0)
{
v___y_1558_ = v___x_1565_;
goto v___jp_1557_;
}
else
{
uint8_t v___x_1566_; 
v___x_1566_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_value_1554_, v_newVal_1550_);
v___y_1558_ = v___x_1566_;
goto v___jp_1557_;
}
v___jp_1557_:
{
if (v___y_1558_ == 0)
{
lean_object* v___x_1559_; 
lean_inc(v_declName_1552_);
lean_dec_ref(v_e_1548_);
v___x_1559_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1546_, v_inst_1547_, v_declName_1552_, v_newType_1549_, v_newVal_1550_, v_newBody_1551_, v_nondep_1556_);
return v___x_1559_;
}
else
{
uint8_t v___x_1560_; 
v___x_1560_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1555_, v_newBody_1551_);
if (v___x_1560_ == 0)
{
lean_object* v___x_1561_; 
lean_inc(v_declName_1552_);
lean_dec_ref(v_e_1548_);
v___x_1561_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1546_, v_inst_1547_, v_declName_1552_, v_newType_1549_, v_newVal_1550_, v_newBody_1551_, v_nondep_1556_);
return v___x_1561_;
}
else
{
lean_object* v_toApplicative_1562_; lean_object* v_toPure_1563_; lean_object* v___x_1564_; 
lean_dec_ref(v_newBody_1551_);
lean_dec_ref(v_newVal_1550_);
lean_dec_ref(v_newType_1549_);
lean_dec_ref(v_inst_1546_);
v_toApplicative_1562_ = lean_ctor_get(v_inst_1547_, 0);
lean_inc_ref(v_toApplicative_1562_);
lean_dec_ref(v_inst_1547_);
v_toPure_1563_ = lean_ctor_get(v_toApplicative_1562_, 1);
lean_inc(v_toPure_1563_);
lean_dec_ref(v_toApplicative_1562_);
v___x_1564_ = lean_apply_2(v_toPure_1563_, lean_box(0), v_e_1548_);
return v___x_1564_;
}
}
}
}
else
{
lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; 
lean_dec_ref(v_newBody_1551_);
lean_dec_ref(v_newVal_1550_);
lean_dec_ref(v_newType_1549_);
lean_dec_ref(v_e_1548_);
lean_dec_ref(v_inst_1546_);
v___x_1567_ = l_Lean_instInhabitedExpr;
v___x_1568_ = l_instInhabitedOfMonad___redArg(v_inst_1547_, v___x_1567_);
v___x_1569_ = lean_obj_once(&l_Lean_Expr_updateLetS_x21___redArg___closed__2, &l_Lean_Expr_updateLetS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateLetS_x21___redArg___closed__2);
v___x_1570_ = l_panic___redArg(v___x_1568_, v___x_1569_);
return v___x_1570_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___redArg___lam__0(lean_object* v_inst_1571_, lean_object* v_inst_1572_, lean_object* v_a_u2082_1573_, lean_object* v_____do__lift_1574_){
_start:
{
lean_object* v___x_1575_; 
v___x_1575_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1571_, v_inst_1572_, v_____do__lift_1574_, v_a_u2082_1573_);
return v___x_1575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___redArg(lean_object* v_inst_1576_, lean_object* v_inst_1577_, lean_object* v_f_1578_, lean_object* v_a_u2081_1579_, lean_object* v_a_u2082_1580_){
_start:
{
lean_object* v_toBind_1581_; lean_object* v___f_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; 
v_toBind_1581_ = lean_ctor_get(v_inst_1577_, 1);
lean_inc(v_toBind_1581_);
lean_inc_ref(v_inst_1577_);
lean_inc_ref(v_inst_1576_);
v___f_1582_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2082___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1582_, 0, v_inst_1576_);
lean_closure_set(v___f_1582_, 1, v_inst_1577_);
lean_closure_set(v___f_1582_, 2, v_a_u2082_1580_);
v___x_1583_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1576_, v_inst_1577_, v_f_1578_, v_a_u2081_1579_);
v___x_1584_ = lean_apply_4(v_toBind_1581_, lean_box(0), lean_box(0), v___x_1583_, v___f_1582_);
return v___x_1584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082(lean_object* v_m_1585_, lean_object* v_inst_1586_, lean_object* v_inst_1587_, lean_object* v_f_1588_, lean_object* v_a_u2081_1589_, lean_object* v_a_u2082_1590_){
_start:
{
lean_object* v___x_1591_; 
v___x_1591_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___redArg(v_inst_1586_, v_inst_1587_, v_f_1588_, v_a_u2081_1589_, v_a_u2082_1590_);
return v___x_1591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___redArg___lam__0(lean_object* v_inst_1592_, lean_object* v_inst_1593_, lean_object* v_a_u2083_1594_, lean_object* v_____do__lift_1595_){
_start:
{
lean_object* v___x_1596_; 
v___x_1596_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1592_, v_inst_1593_, v_____do__lift_1595_, v_a_u2083_1594_);
return v___x_1596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___redArg(lean_object* v_inst_1597_, lean_object* v_inst_1598_, lean_object* v_f_1599_, lean_object* v_a_u2081_1600_, lean_object* v_a_u2082_1601_, lean_object* v_a_u2083_1602_){
_start:
{
lean_object* v_toBind_1603_; lean_object* v___f_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; 
v_toBind_1603_ = lean_ctor_get(v_inst_1598_, 1);
lean_inc(v_toBind_1603_);
lean_inc_ref(v_inst_1598_);
lean_inc_ref(v_inst_1597_);
v___f_1604_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2083___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1604_, 0, v_inst_1597_);
lean_closure_set(v___f_1604_, 1, v_inst_1598_);
lean_closure_set(v___f_1604_, 2, v_a_u2083_1602_);
v___x_1605_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___redArg(v_inst_1597_, v_inst_1598_, v_f_1599_, v_a_u2081_1600_, v_a_u2082_1601_);
v___x_1606_ = lean_apply_4(v_toBind_1603_, lean_box(0), lean_box(0), v___x_1605_, v___f_1604_);
return v___x_1606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083(lean_object* v_m_1607_, lean_object* v_inst_1608_, lean_object* v_inst_1609_, lean_object* v_f_1610_, lean_object* v_a_u2081_1611_, lean_object* v_a_u2082_1612_, lean_object* v_a_u2083_1613_){
_start:
{
lean_object* v___x_1614_; 
v___x_1614_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___redArg(v_inst_1608_, v_inst_1609_, v_f_1610_, v_a_u2081_1611_, v_a_u2082_1612_, v_a_u2083_1613_);
return v___x_1614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___redArg___lam__0(lean_object* v_inst_1615_, lean_object* v_inst_1616_, lean_object* v_a_u2084_1617_, lean_object* v_____do__lift_1618_){
_start:
{
lean_object* v___x_1619_; 
v___x_1619_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1615_, v_inst_1616_, v_____do__lift_1618_, v_a_u2084_1617_);
return v___x_1619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___redArg(lean_object* v_inst_1620_, lean_object* v_inst_1621_, lean_object* v_f_1622_, lean_object* v_a_u2081_1623_, lean_object* v_a_u2082_1624_, lean_object* v_a_u2083_1625_, lean_object* v_a_u2084_1626_){
_start:
{
lean_object* v_toBind_1627_; lean_object* v___f_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; 
v_toBind_1627_ = lean_ctor_get(v_inst_1621_, 1);
lean_inc(v_toBind_1627_);
lean_inc_ref(v_inst_1621_);
lean_inc_ref(v_inst_1620_);
v___f_1628_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2084___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1628_, 0, v_inst_1620_);
lean_closure_set(v___f_1628_, 1, v_inst_1621_);
lean_closure_set(v___f_1628_, 2, v_a_u2084_1626_);
v___x_1629_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___redArg(v_inst_1620_, v_inst_1621_, v_f_1622_, v_a_u2081_1623_, v_a_u2082_1624_, v_a_u2083_1625_);
v___x_1630_ = lean_apply_4(v_toBind_1627_, lean_box(0), lean_box(0), v___x_1629_, v___f_1628_);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084(lean_object* v_m_1631_, lean_object* v_inst_1632_, lean_object* v_inst_1633_, lean_object* v_f_1634_, lean_object* v_a_u2081_1635_, lean_object* v_a_u2082_1636_, lean_object* v_a_u2083_1637_, lean_object* v_a_u2084_1638_){
_start:
{
lean_object* v___x_1639_; 
v___x_1639_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___redArg(v_inst_1632_, v_inst_1633_, v_f_1634_, v_a_u2081_1635_, v_a_u2082_1636_, v_a_u2083_1637_, v_a_u2084_1638_);
return v___x_1639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2085___redArg___lam__0(lean_object* v_inst_1640_, lean_object* v_inst_1641_, lean_object* v_a_u2085_1642_, lean_object* v_____do__lift_1643_){
_start:
{
lean_object* v___x_1644_; 
v___x_1644_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1640_, v_inst_1641_, v_____do__lift_1643_, v_a_u2085_1642_);
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2085___redArg(lean_object* v_inst_1645_, lean_object* v_inst_1646_, lean_object* v_f_1647_, lean_object* v_a_u2081_1648_, lean_object* v_a_u2082_1649_, lean_object* v_a_u2083_1650_, lean_object* v_a_u2084_1651_, lean_object* v_a_u2085_1652_){
_start:
{
lean_object* v_toBind_1653_; lean_object* v___f_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; 
v_toBind_1653_ = lean_ctor_get(v_inst_1646_, 1);
lean_inc(v_toBind_1653_);
lean_inc_ref(v_inst_1646_);
lean_inc_ref(v_inst_1645_);
v___f_1654_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2085___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1654_, 0, v_inst_1645_);
lean_closure_set(v___f_1654_, 1, v_inst_1646_);
lean_closure_set(v___f_1654_, 2, v_a_u2085_1652_);
v___x_1655_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___redArg(v_inst_1645_, v_inst_1646_, v_f_1647_, v_a_u2081_1648_, v_a_u2082_1649_, v_a_u2083_1650_, v_a_u2084_1651_);
v___x_1656_ = lean_apply_4(v_toBind_1653_, lean_box(0), lean_box(0), v___x_1655_, v___f_1654_);
return v___x_1656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2085(lean_object* v_m_1657_, lean_object* v_inst_1658_, lean_object* v_inst_1659_, lean_object* v_f_1660_, lean_object* v_a_u2081_1661_, lean_object* v_a_u2082_1662_, lean_object* v_a_u2083_1663_, lean_object* v_a_u2084_1664_, lean_object* v_a_u2085_1665_){
_start:
{
lean_object* v___x_1666_; 
v___x_1666_ = l_Lean_Meta_Sym_Internal_mkAppS_u2085___redArg(v_inst_1658_, v_inst_1659_, v_f_1660_, v_a_u2081_1661_, v_a_u2082_1662_, v_a_u2083_1663_, v_a_u2084_1664_, v_a_u2085_1665_);
return v___x_1666_;
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
