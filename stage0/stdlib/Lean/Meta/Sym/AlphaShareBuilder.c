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
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_Sym_instBEqExprPtr___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instHashableExprPtr___lam__0___boxed(lean_object*);
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instInhabited___redArg___lam__0(lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_runShareCommonM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instInhabitedSymM(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_EStateM_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_seqRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instMonad___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instMonad___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_ReaderT_read___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lit___override(lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* l_Lean_Meta_Sym_isDebugEnabled___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_Meta_Sym_Internal_Sym_share1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_Meta_Sym_Internal_Sym_share1___redArg___closed__0;
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
static lean_once_cell_t l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__0;
static const lean_string_object l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Lean.Meta.Sym.Internal.liftBuilderM"};
static const lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__1_value;
static const lean_string_object l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_share1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_share1(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_share1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_instBEqExprPtr___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__0 = (const lean_object*)&l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__0_value;
static const lean_closure_object l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_instHashableExprPtr___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__1 = (const lean_object*)&l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_assertShared(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_assertShared___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonad___lam__0, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__0_value;
static const lean_closure_object l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonad___lam__1, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__1_value;
static const lean_closure_object l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonad___lam__2, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__2_value;
static const lean_closure_object l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_map, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__3_value),((lean_object*)&l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__0_value)}};
static const lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__4 = (const lean_object*)&l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__4_value;
static const lean_closure_object l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_pure, .m_arity = 5, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__5 = (const lean_object*)&l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__5_value;
static const lean_closure_object l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_seqRight, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__6 = (const lean_object*)&l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__4_value),((lean_object*)&l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__5_value),((lean_object*)&l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__1_value),((lean_object*)&l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__2_value),((lean_object*)&l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__6_value)}};
static const lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__7 = (const lean_object*)&l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__7_value;
static const lean_closure_object l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_bind, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__8 = (const lean_object*)&l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__7_value),((lean_object*)&l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__8_value)}};
static const lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__9 = (const lean_object*)&l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__9_value;
static lean_once_cell_t l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__10;
static const lean_closure_object l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Internal_Builder_share1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__11 = (const lean_object*)&l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__11_value;
static const lean_closure_object l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Internal_Builder_assertShared___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__12 = (const lean_object*)&l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__12_value;
static lean_once_cell_t l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__13;
static lean_once_cell_t l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__14;
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
lean_object* v_ks_137_; lean_object* v_vs_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_156_; 
v_ks_137_ = lean_ctor_get(v_x_86_, 0);
v_vs_138_ = lean_ctor_get(v_x_86_, 1);
v_isSharedCheck_156_ = !lean_is_exclusive(v_x_86_);
if (v_isSharedCheck_156_ == 0)
{
v___x_140_ = v_x_86_;
v_isShared_141_ = v_isSharedCheck_156_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_vs_138_);
lean_inc(v_ks_137_);
lean_dec(v_x_86_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_156_;
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
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v_ks_137_);
lean_ctor_set(v_reuseFailAlloc_155_, 1, v_vs_138_);
v___x_143_ = v_reuseFailAlloc_155_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
lean_object* v_newNode_144_; size_t v___x_145_; uint8_t v___x_146_; 
v_newNode_144_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__3___redArg(v___x_143_, v_x_89_, v_x_90_);
v___x_145_ = ((size_t)7ULL);
v___x_146_ = lean_usize_dec_le(v___x_145_, v_x_88_);
if (v___x_146_ == 0)
{
lean_object* v___x_147_; lean_object* v___x_148_; uint8_t v___x_149_; 
v___x_147_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_144_);
v___x_148_ = lean_unsigned_to_nat(4u);
v___x_149_ = lean_nat_dec_lt(v___x_147_, v___x_148_);
lean_dec(v___x_147_);
if (v___x_149_ == 0)
{
lean_object* v_ks_150_; lean_object* v_vs_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v_ks_150_ = lean_ctor_get(v_newNode_144_, 0);
lean_inc_ref(v_ks_150_);
v_vs_151_ = lean_ctor_get(v_newNode_144_, 1);
lean_inc_ref(v_vs_151_);
lean_dec_ref(v_newNode_144_);
v___x_152_ = lean_unsigned_to_nat(0u);
v___x_153_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__0);
v___x_154_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4___redArg(v_x_88_, v_ks_150_, v_vs_151_, v___x_152_, v___x_153_);
lean_dec_ref(v_vs_151_);
lean_dec_ref(v_ks_150_);
return v___x_154_;
}
else
{
return v_newNode_144_;
}
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
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4___redArg(size_t v_depth_157_, lean_object* v_keys_158_, lean_object* v_vals_159_, lean_object* v_i_160_, lean_object* v_entries_161_){
_start:
{
lean_object* v___x_162_; uint8_t v___x_163_; 
v___x_162_ = lean_array_get_size(v_keys_158_);
v___x_163_ = lean_nat_dec_lt(v_i_160_, v___x_162_);
if (v___x_163_ == 0)
{
lean_dec(v_i_160_);
return v_entries_161_;
}
else
{
lean_object* v_k_164_; lean_object* v_v_165_; uint64_t v___x_166_; size_t v_h_167_; size_t v___x_168_; lean_object* v___x_169_; size_t v___x_170_; size_t v___x_171_; size_t v___x_172_; size_t v_h_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v_k_164_ = lean_array_fget_borrowed(v_keys_158_, v_i_160_);
v_v_165_ = lean_array_fget_borrowed(v_vals_159_, v_i_160_);
v___x_166_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_k_164_);
v_h_167_ = lean_uint64_to_usize(v___x_166_);
v___x_168_ = ((size_t)5ULL);
v___x_169_ = lean_unsigned_to_nat(1u);
v___x_170_ = ((size_t)1ULL);
v___x_171_ = lean_usize_sub(v_depth_157_, v___x_170_);
v___x_172_ = lean_usize_mul(v___x_168_, v___x_171_);
v_h_173_ = lean_usize_shift_right(v_h_167_, v___x_172_);
v___x_174_ = lean_nat_add(v_i_160_, v___x_169_);
lean_dec(v_i_160_);
lean_inc(v_v_165_);
lean_inc(v_k_164_);
v___x_175_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg(v_entries_161_, v_h_173_, v_depth_157_, v_k_164_, v_v_165_);
v_i_160_ = v___x_174_;
v_entries_161_ = v___x_175_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_depth_177_, lean_object* v_keys_178_, lean_object* v_vals_179_, lean_object* v_i_180_, lean_object* v_entries_181_){
_start:
{
size_t v_depth_boxed_182_; lean_object* v_res_183_; 
v_depth_boxed_182_ = lean_unbox_usize(v_depth_177_);
lean_dec(v_depth_177_);
v_res_183_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4___redArg(v_depth_boxed_182_, v_keys_178_, v_vals_179_, v_i_180_, v_entries_181_);
lean_dec_ref(v_vals_179_);
lean_dec_ref(v_keys_178_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___boxed(lean_object* v_x_184_, lean_object* v_x_185_, lean_object* v_x_186_, lean_object* v_x_187_, lean_object* v_x_188_){
_start:
{
size_t v_x_2065__boxed_189_; size_t v_x_2066__boxed_190_; lean_object* v_res_191_; 
v_x_2065__boxed_189_ = lean_unbox_usize(v_x_185_);
lean_dec(v_x_185_);
v_x_2066__boxed_190_ = lean_unbox_usize(v_x_186_);
lean_dec(v_x_186_);
v_res_191_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg(v_x_184_, v_x_2065__boxed_189_, v_x_2066__boxed_190_, v_x_187_, v_x_188_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1___redArg(lean_object* v_x_192_, lean_object* v_x_193_, lean_object* v_x_194_){
_start:
{
uint64_t v___x_195_; size_t v___x_196_; size_t v___x_197_; lean_object* v___x_198_; 
v___x_195_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_193_);
v___x_196_ = lean_uint64_to_usize(v___x_195_);
v___x_197_ = ((size_t)1ULL);
v___x_198_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg(v_x_192_, v___x_196_, v___x_197_, v_x_193_, v_x_194_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0___redArg(lean_object* v_keys_199_, lean_object* v_i_200_, lean_object* v_k_201_, lean_object* v_k_u2080_202_){
_start:
{
lean_object* v___x_203_; uint8_t v___x_204_; 
v___x_203_ = lean_array_get_size(v_keys_199_);
v___x_204_ = lean_nat_dec_lt(v_i_200_, v___x_203_);
if (v___x_204_ == 0)
{
lean_dec(v_i_200_);
lean_inc_ref(v_k_u2080_202_);
return v_k_u2080_202_;
}
else
{
lean_object* v_k_x27_205_; uint8_t v___x_206_; 
v_k_x27_205_ = lean_array_fget_borrowed(v_keys_199_, v_i_200_);
v___x_206_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_k_201_, v_k_x27_205_);
if (v___x_206_ == 0)
{
lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_207_ = lean_unsigned_to_nat(1u);
v___x_208_ = lean_nat_add(v_i_200_, v___x_207_);
lean_dec(v_i_200_);
v_i_200_ = v___x_208_;
goto _start;
}
else
{
lean_dec(v_i_200_);
lean_inc(v_k_x27_205_);
return v_k_x27_205_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0___redArg___boxed(lean_object* v_keys_210_, lean_object* v_i_211_, lean_object* v_k_212_, lean_object* v_k_u2080_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0___redArg(v_keys_210_, v_i_211_, v_k_212_, v_k_u2080_213_);
lean_dec_ref(v_k_u2080_213_);
lean_dec_ref(v_k_212_);
lean_dec_ref(v_keys_210_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg(lean_object* v_x_215_, size_t v_x_216_, lean_object* v_x_217_, lean_object* v_x_218_){
_start:
{
if (lean_obj_tag(v_x_215_) == 0)
{
lean_object* v_es_219_; lean_object* v___x_220_; size_t v___x_221_; size_t v___x_222_; lean_object* v_j_223_; lean_object* v___x_224_; 
v_es_219_ = lean_ctor_get(v_x_215_, 0);
v___x_220_ = lean_box(2);
v___x_221_ = ((size_t)31ULL);
v___x_222_ = lean_usize_land(v_x_216_, v___x_221_);
v_j_223_ = lean_usize_to_nat(v___x_222_);
v___x_224_ = lean_array_get_borrowed(v___x_220_, v_es_219_, v_j_223_);
lean_dec(v_j_223_);
switch(lean_obj_tag(v___x_224_))
{
case 0:
{
lean_object* v_key_225_; uint8_t v___x_226_; 
v_key_225_ = lean_ctor_get(v___x_224_, 0);
v___x_226_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_217_, v_key_225_);
if (v___x_226_ == 0)
{
lean_inc_ref(v_x_218_);
return v_x_218_;
}
else
{
lean_inc(v_key_225_);
return v_key_225_;
}
}
case 1:
{
lean_object* v_node_227_; size_t v___x_228_; size_t v___x_229_; 
v_node_227_ = lean_ctor_get(v___x_224_, 0);
v___x_228_ = ((size_t)5ULL);
v___x_229_ = lean_usize_shift_right(v_x_216_, v___x_228_);
v_x_215_ = v_node_227_;
v_x_216_ = v___x_229_;
goto _start;
}
default: 
{
lean_inc_ref(v_x_218_);
return v_x_218_;
}
}
}
else
{
lean_object* v_ks_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v_ks_231_ = lean_ctor_get(v_x_215_, 0);
v___x_232_ = lean_unsigned_to_nat(0u);
v___x_233_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0___redArg(v_ks_231_, v___x_232_, v_x_217_, v_x_218_);
return v___x_233_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg___boxed(lean_object* v_x_234_, lean_object* v_x_235_, lean_object* v_x_236_, lean_object* v_x_237_){
_start:
{
size_t v_x_2243__boxed_238_; lean_object* v_res_239_; 
v_x_2243__boxed_238_ = lean_unbox_usize(v_x_235_);
lean_dec(v_x_235_);
v_res_239_ = l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg(v_x_234_, v_x_2243__boxed_238_, v_x_236_, v_x_237_);
lean_dec_ref(v_x_237_);
lean_dec_ref(v_x_236_);
lean_dec_ref(v_x_234_);
return v_res_239_;
}
}
static size_t _init_l_Lean_Meta_Sym_Internal_Sym_share1___redArg___closed__0(void){
_start:
{
lean_object* v___x_240_; size_t v___x_241_; 
v___x_240_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy;
v___x_241_ = lean_ptr_addr(v___x_240_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object* v_e_242_, lean_object* v_a_243_){
_start:
{
lean_object* v___x_245_; lean_object* v_share_246_; lean_object* v___x_247_; uint64_t v___x_248_; size_t v___x_249_; lean_object* v___x_250_; size_t v___x_251_; size_t v___x_252_; uint8_t v___x_253_; 
v___x_245_ = lean_st_ref_get(v_a_243_);
v_share_246_ = lean_ctor_get(v___x_245_, 0);
lean_inc_ref(v_share_246_);
lean_dec(v___x_245_);
v___x_247_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy;
v___x_248_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_242_);
v___x_249_ = lean_uint64_to_usize(v___x_248_);
v___x_250_ = l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg(v_share_246_, v___x_249_, v_e_242_, v___x_247_);
lean_dec_ref(v_share_246_);
v___x_251_ = lean_ptr_addr(v___x_250_);
v___x_252_ = lean_usize_once(&l_Lean_Meta_Sym_Internal_Sym_share1___redArg___closed__0, &l_Lean_Meta_Sym_Internal_Sym_share1___redArg___closed__0_once, _init_l_Lean_Meta_Sym_Internal_Sym_share1___redArg___closed__0);
v___x_253_ = lean_usize_dec_eq(v___x_251_, v___x_252_);
if (v___x_253_ == 0)
{
lean_object* v___x_254_; 
lean_dec_ref(v_e_242_);
v___x_254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_254_, 0, v___x_250_);
return v___x_254_;
}
else
{
lean_object* v___x_255_; lean_object* v_share_256_; lean_object* v_maxFVar_257_; lean_object* v_proofInstInfo_258_; lean_object* v_inferType_259_; lean_object* v_getLevel_260_; lean_object* v_congrInfo_261_; lean_object* v_defEqI_262_; lean_object* v_extensions_263_; lean_object* v_issues_264_; lean_object* v_canon_265_; lean_object* v_instanceOverrides_266_; uint8_t v_debug_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_278_; 
lean_dec_ref(v___x_250_);
v___x_255_ = lean_st_ref_take(v_a_243_);
v_share_256_ = lean_ctor_get(v___x_255_, 0);
v_maxFVar_257_ = lean_ctor_get(v___x_255_, 1);
v_proofInstInfo_258_ = lean_ctor_get(v___x_255_, 2);
v_inferType_259_ = lean_ctor_get(v___x_255_, 3);
v_getLevel_260_ = lean_ctor_get(v___x_255_, 4);
v_congrInfo_261_ = lean_ctor_get(v___x_255_, 5);
v_defEqI_262_ = lean_ctor_get(v___x_255_, 6);
v_extensions_263_ = lean_ctor_get(v___x_255_, 7);
v_issues_264_ = lean_ctor_get(v___x_255_, 8);
v_canon_265_ = lean_ctor_get(v___x_255_, 9);
v_instanceOverrides_266_ = lean_ctor_get(v___x_255_, 10);
v_debug_267_ = lean_ctor_get_uint8(v___x_255_, sizeof(void*)*11);
v_isSharedCheck_278_ = !lean_is_exclusive(v___x_255_);
if (v_isSharedCheck_278_ == 0)
{
v___x_269_ = v___x_255_;
v_isShared_270_ = v_isSharedCheck_278_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_instanceOverrides_266_);
lean_inc(v_canon_265_);
lean_inc(v_issues_264_);
lean_inc(v_extensions_263_);
lean_inc(v_defEqI_262_);
lean_inc(v_congrInfo_261_);
lean_inc(v_getLevel_260_);
lean_inc(v_inferType_259_);
lean_inc(v_proofInstInfo_258_);
lean_inc(v_maxFVar_257_);
lean_inc(v_share_256_);
lean_dec(v___x_255_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_278_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_274_; 
v___x_271_ = lean_box(0);
lean_inc_ref(v_e_242_);
v___x_272_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1___redArg(v_share_256_, v_e_242_, v___x_271_);
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 0, v___x_272_);
v___x_274_ = v___x_269_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v___x_272_);
lean_ctor_set(v_reuseFailAlloc_277_, 1, v_maxFVar_257_);
lean_ctor_set(v_reuseFailAlloc_277_, 2, v_proofInstInfo_258_);
lean_ctor_set(v_reuseFailAlloc_277_, 3, v_inferType_259_);
lean_ctor_set(v_reuseFailAlloc_277_, 4, v_getLevel_260_);
lean_ctor_set(v_reuseFailAlloc_277_, 5, v_congrInfo_261_);
lean_ctor_set(v_reuseFailAlloc_277_, 6, v_defEqI_262_);
lean_ctor_set(v_reuseFailAlloc_277_, 7, v_extensions_263_);
lean_ctor_set(v_reuseFailAlloc_277_, 8, v_issues_264_);
lean_ctor_set(v_reuseFailAlloc_277_, 9, v_canon_265_);
lean_ctor_set(v_reuseFailAlloc_277_, 10, v_instanceOverrides_266_);
lean_ctor_set_uint8(v_reuseFailAlloc_277_, sizeof(void*)*11, v_debug_267_);
v___x_274_ = v_reuseFailAlloc_277_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_275_ = lean_st_ref_put(v_a_243_, v___x_274_);
v___x_276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_276_, 0, v_e_242_);
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
size_t v_x_2341__boxed_312_; lean_object* v_res_313_; 
v_x_2341__boxed_312_ = lean_unbox_usize(v_x_309_);
lean_dec(v_x_309_);
v_res_313_ = l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0(v_00_u03b2_307_, v_x_308_, v_x_2341__boxed_312_, v_x_310_, v_x_311_);
lean_dec_ref(v_x_311_);
lean_dec_ref(v_x_310_);
lean_dec_ref(v_x_308_);
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
lean_dec_ref(v_k_332_);
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
size_t v_x_2365__boxed_348_; size_t v_x_2366__boxed_349_; lean_object* v_res_350_; 
v_x_2365__boxed_348_ = lean_unbox_usize(v_x_344_);
lean_dec(v_x_344_);
v_x_2366__boxed_349_ = lean_unbox_usize(v_x_345_);
lean_dec(v_x_345_);
v_res_350_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2(v_00_u03b2_342_, v_x_343_, v_x_2365__boxed_348_, v_x_2366__boxed_349_, v_x_346_, v_x_347_);
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
v___x_379_ = l_Lean_Meta_Sym_instInhabitedSymM(lean_box(0));
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0(lean_object* v_msg_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_){
_start:
{
lean_object* v___x_388_; lean_object* v___x_698__overap_389_; lean_object* v___x_390_; 
v___x_388_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0, &l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0);
v___x_698__overap_389_ = lean_panic_fn_borrowed(v___x_388_, v_msg_380_);
lean_inc(v___y_386_);
lean_inc_ref(v___y_385_);
lean_inc(v___y_384_);
lean_inc_ref(v___y_383_);
lean_inc(v___y_382_);
lean_inc_ref(v___y_381_);
v___x_390_ = lean_apply_7(v___x_698__overap_389_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, lean_box(0));
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___boxed(lean_object* v_msg_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0(v_msg_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_);
lean_dec(v___y_397_);
lean_dec_ref(v___y_396_);
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
return v_res_399_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__3(void){
_start:
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_403_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__2));
v___x_404_ = lean_unsigned_to_nat(2u);
v___x_405_ = lean_unsigned_to_nat(42u);
v___x_406_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__1));
v___x_407_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_408_ = l_mkPanicMessageWithDecl(v___x_407_, v___x_406_, v___x_405_, v___x_404_, v___x_403_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object* v_e_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_){
_start:
{
lean_object* v___x_417_; lean_object* v_share_418_; lean_object* v___x_419_; uint64_t v___x_420_; size_t v___x_421_; lean_object* v___x_422_; size_t v___x_423_; size_t v___x_424_; uint8_t v___x_425_; 
v___x_417_ = lean_st_ref_get(v_a_411_);
v_share_418_ = lean_ctor_get(v___x_417_, 0);
lean_inc_ref(v_share_418_);
lean_dec(v___x_417_);
v___x_419_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy;
v___x_420_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_409_);
v___x_421_ = lean_uint64_to_usize(v___x_420_);
v___x_422_ = l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg(v_share_418_, v___x_421_, v_e_409_, v___x_419_);
lean_dec_ref(v_share_418_);
v___x_423_ = lean_ptr_addr(v___x_422_);
lean_dec_ref(v___x_422_);
v___x_424_ = lean_ptr_addr(v_e_409_);
v___x_425_ = lean_usize_dec_eq(v___x_423_, v___x_424_);
if (v___x_425_ == 0)
{
lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_426_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__3, &l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__3_once, _init_l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__3);
v___x_427_ = l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0(v___x_426_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_);
return v___x_427_;
}
else
{
lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_428_ = lean_box(0);
v___x_429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_429_, 0, v___x_428_);
return v___x_429_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared___boxed(lean_object* v_e_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_e_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_, v_a_436_);
lean_dec(v_a_436_);
lean_dec_ref(v_a_435_);
lean_dec(v_a_434_);
lean_dec_ref(v_a_433_);
lean_dec(v_a_432_);
lean_dec_ref(v_a_431_);
lean_dec_ref(v_e_430_);
return v_res_438_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__0(void){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = l_Lean_Meta_Sym_instInhabitedSymM(lean_box(0));
return v___x_447_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__3(void){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_450_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2));
v___x_451_ = lean_unsigned_to_nat(16u);
v___x_452_ = lean_unsigned_to_nat(62u);
v___x_453_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__1));
v___x_454_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_455_ = l_mkPanicMessageWithDecl(v___x_454_, v___x_453_, v___x_452_, v___x_451_, v___x_450_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM___redArg(lean_object* v_k_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_){
_start:
{
lean_object* v___x_464_; lean_object* v___x_465_; uint8_t v_debug_466_; lean_object* v_env_467_; lean_object* v___x_468_; lean_object* v___x_469_; uint8_t v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_464_ = lean_st_ref_get(v_a_458_);
v___x_465_ = lean_st_ref_get(v_a_462_);
v_debug_466_ = lean_ctor_get_uint8(v___x_464_, sizeof(void*)*11);
lean_dec(v___x_464_);
v_env_467_ = lean_ctor_get(v___x_465_, 0);
lean_inc_ref(v_env_467_);
lean_dec(v___x_465_);
v___x_468_ = lean_box(v_debug_466_);
v___x_469_ = lean_apply_1(v_k_456_, v___x_468_);
v___x_470_ = 0;
v___x_471_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_471_, 0, v_env_467_);
lean_ctor_set_uint8(v___x_471_, sizeof(void*)*1, v___x_470_);
lean_ctor_set_uint8(v___x_471_, sizeof(void*)*1 + 1, v___x_470_);
v___x_472_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___x_469_, v___x_471_, v_a_458_);
if (lean_obj_tag(v___x_472_) == 0)
{
lean_object* v_a_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_485_; 
v_a_473_ = lean_ctor_get(v___x_472_, 0);
v_isSharedCheck_485_ = !lean_is_exclusive(v___x_472_);
if (v_isSharedCheck_485_ == 0)
{
v___x_475_ = v___x_472_;
v_isShared_476_ = v_isSharedCheck_485_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_a_473_);
lean_dec(v___x_472_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_485_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
if (lean_obj_tag(v_a_473_) == 0)
{
lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_1305__overap_479_; lean_object* v___x_480_; 
lean_dec_ref_known(v_a_473_, 1);
lean_del_object(v___x_475_);
v___x_477_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__0, &l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__0_once, _init_l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__0);
v___x_478_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__3, &l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__3_once, _init_l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__3);
v___x_1305__overap_479_ = l_panic___redArg(v___x_477_, v___x_478_);
lean_inc(v_a_462_);
lean_inc_ref(v_a_461_);
lean_inc(v_a_460_);
lean_inc_ref(v_a_459_);
lean_inc(v_a_458_);
lean_inc_ref(v_a_457_);
v___x_480_ = lean_apply_7(v___x_1305__overap_479_, v_a_457_, v_a_458_, v_a_459_, v_a_460_, v_a_461_, v_a_462_, lean_box(0));
return v___x_480_;
}
else
{
lean_object* v_a_481_; lean_object* v___x_483_; 
v_a_481_ = lean_ctor_get(v_a_473_, 0);
lean_inc(v_a_481_);
lean_dec_ref_known(v_a_473_, 1);
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 0, v_a_481_);
v___x_483_ = v___x_475_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v_a_481_);
v___x_483_ = v_reuseFailAlloc_484_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
return v___x_483_;
}
}
}
}
else
{
lean_object* v_a_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_493_; 
v_a_486_ = lean_ctor_get(v___x_472_, 0);
v_isSharedCheck_493_ = !lean_is_exclusive(v___x_472_);
if (v_isSharedCheck_493_ == 0)
{
v___x_488_ = v___x_472_;
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_a_486_);
lean_dec(v___x_472_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_491_; 
if (v_isShared_489_ == 0)
{
v___x_491_ = v___x_488_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_a_486_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___boxed(lean_object* v_k_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l_Lean_Meta_Sym_Internal_liftBuilderM___redArg(v_k_494_, v_a_495_, v_a_496_, v_a_497_, v_a_498_, v_a_499_, v_a_500_);
lean_dec(v_a_500_);
lean_dec_ref(v_a_499_);
lean_dec(v_a_498_);
lean_dec_ref(v_a_497_);
lean_dec(v_a_496_);
lean_dec_ref(v_a_495_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM(lean_object* v_00_u03b1_503_, lean_object* v_k_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_){
_start:
{
lean_object* v___x_512_; lean_object* v___x_513_; uint8_t v_debug_514_; lean_object* v_env_515_; lean_object* v___x_516_; lean_object* v___x_517_; uint8_t v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_512_ = lean_st_ref_get(v_a_506_);
v___x_513_ = lean_st_ref_get(v_a_510_);
v_debug_514_ = lean_ctor_get_uint8(v___x_512_, sizeof(void*)*11);
lean_dec(v___x_512_);
v_env_515_ = lean_ctor_get(v___x_513_, 0);
lean_inc_ref(v_env_515_);
lean_dec(v___x_513_);
v___x_516_ = lean_box(v_debug_514_);
v___x_517_ = lean_apply_1(v_k_504_, v___x_516_);
v___x_518_ = 0;
v___x_519_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_519_, 0, v_env_515_);
lean_ctor_set_uint8(v___x_519_, sizeof(void*)*1, v___x_518_);
lean_ctor_set_uint8(v___x_519_, sizeof(void*)*1 + 1, v___x_518_);
v___x_520_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___x_517_, v___x_519_, v_a_506_);
if (lean_obj_tag(v___x_520_) == 0)
{
lean_object* v_a_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_533_; 
v_a_521_ = lean_ctor_get(v___x_520_, 0);
v_isSharedCheck_533_ = !lean_is_exclusive(v___x_520_);
if (v_isSharedCheck_533_ == 0)
{
v___x_523_ = v___x_520_;
v_isShared_524_ = v_isSharedCheck_533_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_a_521_);
lean_dec(v___x_520_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_533_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
if (lean_obj_tag(v_a_521_) == 0)
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_1333__overap_527_; lean_object* v___x_528_; 
lean_dec_ref_known(v_a_521_, 1);
lean_del_object(v___x_523_);
v___x_525_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__0, &l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__0_once, _init_l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__0);
v___x_526_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__3, &l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__3_once, _init_l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__3);
v___x_1333__overap_527_ = l_panic___redArg(v___x_525_, v___x_526_);
lean_inc(v_a_510_);
lean_inc_ref(v_a_509_);
lean_inc(v_a_508_);
lean_inc_ref(v_a_507_);
lean_inc(v_a_506_);
lean_inc_ref(v_a_505_);
v___x_528_ = lean_apply_7(v___x_1333__overap_527_, v_a_505_, v_a_506_, v_a_507_, v_a_508_, v_a_509_, v_a_510_, lean_box(0));
return v___x_528_;
}
else
{
lean_object* v_a_529_; lean_object* v___x_531_; 
v_a_529_ = lean_ctor_get(v_a_521_, 0);
lean_inc(v_a_529_);
lean_dec_ref_known(v_a_521_, 1);
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 0, v_a_529_);
v___x_531_ = v___x_523_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v_a_529_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
return v___x_531_;
}
}
}
}
else
{
lean_object* v_a_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_541_; 
v_a_534_ = lean_ctor_get(v___x_520_, 0);
v_isSharedCheck_541_ = !lean_is_exclusive(v___x_520_);
if (v_isSharedCheck_541_ == 0)
{
v___x_536_ = v___x_520_;
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_a_534_);
lean_dec(v___x_520_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_539_; 
if (v_isShared_537_ == 0)
{
v___x_539_ = v___x_536_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v_a_534_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM___boxed(lean_object* v_00_u03b1_542_, lean_object* v_k_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = l_Lean_Meta_Sym_Internal_liftBuilderM(v_00_u03b1_542_, v_k_543_, v_a_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_);
lean_dec(v_a_549_);
lean_dec_ref(v_a_548_);
lean_dec(v_a_547_);
lean_dec_ref(v_a_546_);
lean_dec(v_a_545_);
lean_dec_ref(v_a_544_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_share1___redArg(lean_object* v_e_552_, lean_object* v_a_553_){
_start:
{
lean_object* v___x_554_; uint64_t v___x_555_; size_t v___x_556_; lean_object* v___x_557_; size_t v___x_558_; size_t v___x_559_; uint8_t v___x_560_; 
v___x_554_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy;
v___x_555_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_552_);
v___x_556_ = lean_uint64_to_usize(v___x_555_);
v___x_557_ = l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg(v_a_553_, v___x_556_, v_e_552_, v___x_554_);
v___x_558_ = lean_ptr_addr(v___x_557_);
v___x_559_ = lean_usize_once(&l_Lean_Meta_Sym_Internal_Sym_share1___redArg___closed__0, &l_Lean_Meta_Sym_Internal_Sym_share1___redArg___closed__0_once, _init_l_Lean_Meta_Sym_Internal_Sym_share1___redArg___closed__0);
v___x_560_ = lean_usize_dec_eq(v___x_558_, v___x_559_);
if (v___x_560_ == 0)
{
lean_object* v___x_561_; 
lean_dec_ref(v_e_552_);
v___x_561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_561_, 0, v___x_557_);
lean_ctor_set(v___x_561_, 1, v_a_553_);
return v___x_561_;
}
else
{
lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
lean_dec_ref(v___x_557_);
v___x_562_ = lean_box(0);
lean_inc_ref(v_e_552_);
v___x_563_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1___redArg(v_a_553_, v_e_552_, v___x_562_);
v___x_564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_564_, 0, v_e_552_);
lean_ctor_set(v___x_564_, 1, v___x_563_);
return v___x_564_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_share1(lean_object* v_e_565_, uint8_t v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_){
_start:
{
lean_object* v___x_569_; 
v___x_569_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v_e_565_, v_a_568_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_share1___boxed(lean_object* v_e_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_){
_start:
{
uint8_t v_a_boxed_574_; lean_object* v_res_575_; 
v_a_boxed_574_ = lean_unbox(v_a_571_);
v_res_575_ = l_Lean_Meta_Sym_Internal_Builder_share1(v_e_570_, v_a_boxed_574_, v_a_572_, v_a_573_);
lean_dec_ref(v_a_572_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1(lean_object* v_msg_578_, uint8_t v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_){
_start:
{
lean_object* v___f_582_; lean_object* v___f_583_; lean_object* v___x_584_; lean_object* v___f_585_; lean_object* v___f_586_; lean_object* v___f_587_; lean_object* v___x_534__overap_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v___f_582_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__0));
v___f_583_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__1));
v___x_584_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___f_582_, v___f_583_);
v___f_585_ = lean_alloc_closure((void*)(l_EStateM_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_585_, 0, v___x_584_);
v___f_586_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_586_, 0, v___f_585_);
v___f_587_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_587_, 0, v___f_586_);
v___x_534__overap_588_ = lean_panic_fn_borrowed(v___f_587_, v_msg_578_);
lean_dec_ref(v___f_587_);
v___x_589_ = lean_box(v___y_579_);
lean_inc_ref(v___y_580_);
v___x_590_ = lean_apply_3(v___x_534__overap_588_, v___x_589_, v___y_580_, v___y_581_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___boxed(lean_object* v_msg_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_){
_start:
{
uint8_t v___y_636__boxed_595_; lean_object* v_res_596_; 
v___y_636__boxed_595_ = lean_unbox(v___y_592_);
v_res_596_ = l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1(v_msg_591_, v___y_636__boxed_595_, v___y_593_, v___y_594_);
lean_dec_ref(v___y_593_);
return v_res_596_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_597_, lean_object* v_i_598_, lean_object* v_k_599_){
_start:
{
lean_object* v___x_600_; uint8_t v___x_601_; 
v___x_600_ = lean_array_get_size(v_keys_597_);
v___x_601_ = lean_nat_dec_lt(v_i_598_, v___x_600_);
if (v___x_601_ == 0)
{
lean_dec(v_i_598_);
return v___x_601_;
}
else
{
lean_object* v_k_x27_602_; uint8_t v___x_603_; 
v_k_x27_602_ = lean_array_fget_borrowed(v_keys_597_, v_i_598_);
v___x_603_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_k_599_, v_k_x27_602_);
if (v___x_603_ == 0)
{
lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_604_ = lean_unsigned_to_nat(1u);
v___x_605_ = lean_nat_add(v_i_598_, v___x_604_);
lean_dec(v_i_598_);
v_i_598_ = v___x_605_;
goto _start;
}
else
{
lean_dec(v_i_598_);
return v___x_601_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_607_, lean_object* v_i_608_, lean_object* v_k_609_){
_start:
{
uint8_t v_res_610_; lean_object* v_r_611_; 
v_res_610_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg(v_keys_607_, v_i_608_, v_k_609_);
lean_dec_ref(v_k_609_);
lean_dec_ref(v_keys_607_);
v_r_611_ = lean_box(v_res_610_);
return v_r_611_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg(lean_object* v_x_612_, size_t v_x_613_, lean_object* v_x_614_){
_start:
{
if (lean_obj_tag(v_x_612_) == 0)
{
lean_object* v_es_615_; lean_object* v___x_616_; size_t v___x_617_; size_t v___x_618_; lean_object* v_j_619_; lean_object* v___x_620_; 
v_es_615_ = lean_ctor_get(v_x_612_, 0);
v___x_616_ = lean_box(2);
v___x_617_ = ((size_t)31ULL);
v___x_618_ = lean_usize_land(v_x_613_, v___x_617_);
v_j_619_ = lean_usize_to_nat(v___x_618_);
v___x_620_ = lean_array_get_borrowed(v___x_616_, v_es_615_, v_j_619_);
lean_dec(v_j_619_);
switch(lean_obj_tag(v___x_620_))
{
case 0:
{
lean_object* v_key_621_; uint8_t v___x_622_; 
v_key_621_ = lean_ctor_get(v___x_620_, 0);
v___x_622_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_614_, v_key_621_);
return v___x_622_;
}
case 1:
{
lean_object* v_node_623_; size_t v___x_624_; size_t v___x_625_; 
v_node_623_ = lean_ctor_get(v___x_620_, 0);
v___x_624_ = ((size_t)5ULL);
v___x_625_ = lean_usize_shift_right(v_x_613_, v___x_624_);
v_x_612_ = v_node_623_;
v_x_613_ = v___x_625_;
goto _start;
}
default: 
{
uint8_t v___x_627_; 
v___x_627_ = 0;
return v___x_627_;
}
}
}
else
{
lean_object* v_ks_628_; lean_object* v___x_629_; uint8_t v___x_630_; 
v_ks_628_ = lean_ctor_get(v_x_612_, 0);
v___x_629_ = lean_unsigned_to_nat(0u);
v___x_630_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg(v_ks_628_, v___x_629_, v_x_614_);
return v___x_630_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg___boxed(lean_object* v_x_631_, lean_object* v_x_632_, lean_object* v_x_633_){
_start:
{
size_t v_x_676__boxed_634_; uint8_t v_res_635_; lean_object* v_r_636_; 
v_x_676__boxed_634_ = lean_unbox_usize(v_x_632_);
lean_dec(v_x_632_);
v_res_635_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg(v_x_631_, v_x_676__boxed_634_, v_x_633_);
lean_dec_ref(v_x_633_);
lean_dec_ref(v_x_631_);
v_r_636_ = lean_box(v_res_635_);
return v_r_636_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg(lean_object* v_x_637_, lean_object* v_x_638_){
_start:
{
uint64_t v___x_639_; size_t v___x_640_; uint8_t v___x_641_; 
v___x_639_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_638_);
v___x_640_ = lean_uint64_to_usize(v___x_639_);
v___x_641_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg(v_x_637_, v___x_640_, v_x_638_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg___boxed(lean_object* v_x_642_, lean_object* v_x_643_){
_start:
{
uint8_t v_res_644_; lean_object* v_r_645_; 
v_res_644_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg(v_x_642_, v_x_643_);
lean_dec_ref(v_x_643_);
lean_dec_ref(v_x_642_);
v_r_645_ = lean_box(v_res_644_);
return v_r_645_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__2(void){
_start:
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_648_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__1));
v___x_649_ = lean_unsigned_to_nat(2u);
v___x_650_ = lean_unsigned_to_nat(74u);
v___x_651_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__0));
v___x_652_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_653_ = l_mkPanicMessageWithDecl(v___x_652_, v___x_651_, v___x_650_, v___x_649_, v___x_648_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_assertShared(lean_object* v_e_654_, uint8_t v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_){
_start:
{
uint8_t v___x_658_; 
v___x_658_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg(v_a_657_, v_e_654_);
if (v___x_658_ == 0)
{
lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_659_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__2, &l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__2_once, _init_l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__2);
v___x_660_ = l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1(v___x_659_, v_a_655_, v_a_656_, v_a_657_);
return v___x_660_;
}
else
{
lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_661_ = lean_box(0);
v___x_662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_662_, 0, v___x_661_);
lean_ctor_set(v___x_662_, 1, v_a_657_);
return v___x_662_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_assertShared___boxed(lean_object* v_e_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_){
_start:
{
uint8_t v_a_boxed_667_; lean_object* v_res_668_; 
v_a_boxed_667_ = lean_unbox(v_a_664_);
v_res_668_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_e_663_, v_a_boxed_667_, v_a_665_, v_a_666_);
lean_dec_ref(v_a_665_);
lean_dec_ref(v_e_663_);
return v_res_668_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0(lean_object* v_00_u03b2_669_, lean_object* v_x_670_, lean_object* v_x_671_){
_start:
{
uint8_t v___x_672_; 
v___x_672_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg(v_x_670_, v_x_671_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___boxed(lean_object* v_00_u03b2_673_, lean_object* v_x_674_, lean_object* v_x_675_){
_start:
{
uint8_t v_res_676_; lean_object* v_r_677_; 
v_res_676_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0(v_00_u03b2_673_, v_x_674_, v_x_675_);
lean_dec_ref(v_x_675_);
lean_dec_ref(v_x_674_);
v_r_677_ = lean_box(v_res_676_);
return v_r_677_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0(lean_object* v_00_u03b2_678_, lean_object* v_x_679_, size_t v_x_680_, lean_object* v_x_681_){
_start:
{
uint8_t v___x_682_; 
v___x_682_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg(v_x_679_, v_x_680_, v_x_681_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___boxed(lean_object* v_00_u03b2_683_, lean_object* v_x_684_, lean_object* v_x_685_, lean_object* v_x_686_){
_start:
{
size_t v_x_775__boxed_687_; uint8_t v_res_688_; lean_object* v_r_689_; 
v_x_775__boxed_687_ = lean_unbox_usize(v_x_685_);
lean_dec(v_x_685_);
v_res_688_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0(v_00_u03b2_683_, v_x_684_, v_x_775__boxed_687_, v_x_686_);
lean_dec_ref(v_x_686_);
lean_dec_ref(v_x_684_);
v_r_689_ = lean_box(v_res_688_);
return v_r_689_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_690_, lean_object* v_keys_691_, lean_object* v_vals_692_, lean_object* v_heq_693_, lean_object* v_i_694_, lean_object* v_k_695_){
_start:
{
uint8_t v___x_696_; 
v___x_696_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg(v_keys_691_, v_i_694_, v_k_695_);
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_697_, lean_object* v_keys_698_, lean_object* v_vals_699_, lean_object* v_heq_700_, lean_object* v_i_701_, lean_object* v_k_702_){
_start:
{
uint8_t v_res_703_; lean_object* v_r_704_; 
v_res_703_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2(v_00_u03b2_697_, v_keys_698_, v_vals_699_, v_heq_700_, v_i_701_, v_k_702_);
lean_dec_ref(v_k_702_);
lean_dec_ref(v_vals_699_);
lean_dec_ref(v_keys_698_);
v_r_704_ = lean_box(v_res_703_);
return v_r_704_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__10(void){
_start:
{
lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_724_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__9));
v___x_725_ = l_ReaderT_instMonad___redArg(v___x_724_);
return v___x_725_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__13(void){
_start:
{
lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_728_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__10, &l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__10_once, _init_l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__10);
v___x_729_ = lean_alloc_closure((void*)(l_ReaderT_read___boxed), 4, 3);
lean_closure_set(v___x_729_, 0, lean_box(0));
lean_closure_set(v___x_729_, 1, lean_box(0));
lean_closure_set(v___x_729_, 2, v___x_728_);
return v___x_729_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__14(void){
_start:
{
lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_730_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__13, &l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__13_once, _init_l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__13);
v___x_731_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__12));
v___x_732_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__11));
v___x_733_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_733_, 0, v___x_732_);
lean_ctor_set(v___x_733_, 1, v___x_731_);
lean_ctor_set(v___x_733_, 2, v___x_730_);
return v___x_733_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM(void){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__14, &l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__14_once, _init_l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__14);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLitS___redArg(lean_object* v_inst_735_, lean_object* v_l_736_){
_start:
{
lean_object* v_share1_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
v_share1_737_ = lean_ctor_get(v_inst_735_, 0);
lean_inc(v_share1_737_);
lean_dec_ref(v_inst_735_);
v___x_738_ = l_Lean_Expr_lit___override(v_l_736_);
v___x_739_ = lean_apply_1(v_share1_737_, v___x_738_);
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLitS(lean_object* v_m_740_, lean_object* v_inst_741_, lean_object* v_l_742_){
_start:
{
lean_object* v___x_743_; 
v___x_743_ = l_Lean_Meta_Sym_Internal_mkLitS___redArg(v_inst_741_, v_l_742_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___redArg(lean_object* v_inst_744_, lean_object* v_declName_745_, lean_object* v_us_746_){
_start:
{
lean_object* v_share1_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
v_share1_747_ = lean_ctor_get(v_inst_744_, 0);
lean_inc(v_share1_747_);
lean_dec_ref(v_inst_744_);
v___x_748_ = l_Lean_Expr_const___override(v_declName_745_, v_us_746_);
v___x_749_ = lean_apply_1(v_share1_747_, v___x_748_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS(lean_object* v_m_750_, lean_object* v_inst_751_, lean_object* v_declName_752_, lean_object* v_us_753_){
_start:
{
lean_object* v___x_754_; 
v___x_754_ = l_Lean_Meta_Sym_Internal_mkConstS___redArg(v_inst_751_, v_declName_752_, v_us_753_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___redArg(lean_object* v_inst_755_, lean_object* v_idx_756_){
_start:
{
lean_object* v_share1_757_; lean_object* v___x_758_; lean_object* v___x_759_; 
v_share1_757_ = lean_ctor_get(v_inst_755_, 0);
lean_inc(v_share1_757_);
lean_dec_ref(v_inst_755_);
v___x_758_ = l_Lean_Expr_bvar___override(v_idx_756_);
v___x_759_ = lean_apply_1(v_share1_757_, v___x_758_);
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS(lean_object* v_m_760_, lean_object* v_inst_761_, lean_object* v_idx_762_){
_start:
{
lean_object* v___x_763_; 
v___x_763_ = l_Lean_Meta_Sym_Internal_mkBVarS___redArg(v_inst_761_, v_idx_762_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS___redArg(lean_object* v_inst_764_, lean_object* v_u_765_){
_start:
{
lean_object* v_share1_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
v_share1_766_ = lean_ctor_get(v_inst_764_, 0);
lean_inc(v_share1_766_);
lean_dec_ref(v_inst_764_);
v___x_767_ = l_Lean_Expr_sort___override(v_u_765_);
v___x_768_ = lean_apply_1(v_share1_766_, v___x_767_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS(lean_object* v_m_769_, lean_object* v_inst_770_, lean_object* v_u_771_){
_start:
{
lean_object* v___x_772_; 
v___x_772_ = l_Lean_Meta_Sym_Internal_mkSortS___redArg(v_inst_770_, v_u_771_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___redArg(lean_object* v_inst_773_, lean_object* v_fvarId_774_){
_start:
{
lean_object* v_share1_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
v_share1_775_ = lean_ctor_get(v_inst_773_, 0);
lean_inc(v_share1_775_);
lean_dec_ref(v_inst_773_);
v___x_776_ = l_Lean_Expr_fvar___override(v_fvarId_774_);
v___x_777_ = lean_apply_1(v_share1_775_, v___x_776_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS(lean_object* v_m_778_, lean_object* v_inst_779_, lean_object* v_fvarId_780_){
_start:
{
lean_object* v___x_781_; 
v___x_781_ = l_Lean_Meta_Sym_Internal_mkFVarS___redArg(v_inst_779_, v_fvarId_780_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMVarS___redArg(lean_object* v_inst_782_, lean_object* v_mvarId_783_){
_start:
{
lean_object* v_share1_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
v_share1_784_ = lean_ctor_get(v_inst_782_, 0);
lean_inc(v_share1_784_);
lean_dec_ref(v_inst_782_);
v___x_785_ = l_Lean_Expr_mvar___override(v_mvarId_783_);
v___x_786_ = lean_apply_1(v_share1_784_, v___x_785_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMVarS(lean_object* v_m_787_, lean_object* v_inst_788_, lean_object* v_mvarId_789_){
_start:
{
lean_object* v___x_790_; 
v___x_790_ = l_Lean_Meta_Sym_Internal_mkMVarS___redArg(v_inst_788_, v_mvarId_789_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__0(lean_object* v_d_791_, lean_object* v_e_792_, lean_object* v_share1_793_, lean_object* v_____r_794_){
_start:
{
lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_795_ = l_Lean_Expr_mdata___override(v_d_791_, v_e_792_);
v___x_796_ = lean_apply_1(v_share1_793_, v___x_795_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1(lean_object* v___f_797_, lean_object* v_____r_798_){
_start:
{
lean_object* v___x_799_; 
v___x_799_ = lean_apply_1(v___f_797_, v_____r_798_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__2(lean_object* v___f_800_, lean_object* v_assertShared_801_, lean_object* v_e_802_, lean_object* v_toBind_803_, lean_object* v___f_804_, uint8_t v_____do__lift_805_){
_start:
{
if (v_____do__lift_805_ == 0)
{
lean_object* v___x_806_; lean_object* v___x_807_; 
lean_dec(v___f_804_);
lean_dec(v_toBind_803_);
lean_dec_ref(v_e_802_);
lean_dec(v_assertShared_801_);
v___x_806_ = lean_box(0);
v___x_807_ = lean_apply_1(v___f_800_, v___x_806_);
return v___x_807_;
}
else
{
lean_object* v___x_808_; lean_object* v___x_809_; 
lean_dec(v___f_800_);
v___x_808_ = lean_apply_1(v_assertShared_801_, v_e_802_);
v___x_809_ = lean_apply_4(v_toBind_803_, lean_box(0), lean_box(0), v___x_808_, v___f_804_);
return v___x_809_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__2___boxed(lean_object* v___f_810_, lean_object* v_assertShared_811_, lean_object* v_e_812_, lean_object* v_toBind_813_, lean_object* v___f_814_, lean_object* v_____do__lift_815_){
_start:
{
uint8_t v_____do__lift_63__boxed_816_; lean_object* v_res_817_; 
v_____do__lift_63__boxed_816_ = lean_unbox(v_____do__lift_815_);
v_res_817_ = l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__2(v___f_810_, v_assertShared_811_, v_e_812_, v_toBind_813_, v___f_814_, v_____do__lift_63__boxed_816_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg(lean_object* v_inst_818_, lean_object* v_inst_819_, lean_object* v_d_820_, lean_object* v_e_821_){
_start:
{
lean_object* v_toBind_822_; lean_object* v_share1_823_; lean_object* v_assertShared_824_; lean_object* v_isDebugEnabled_825_; lean_object* v___f_826_; lean_object* v___f_827_; lean_object* v___f_828_; lean_object* v___x_829_; 
v_toBind_822_ = lean_ctor_get(v_inst_819_, 1);
lean_inc_n(v_toBind_822_, 2);
lean_dec_ref(v_inst_819_);
v_share1_823_ = lean_ctor_get(v_inst_818_, 0);
lean_inc(v_share1_823_);
v_assertShared_824_ = lean_ctor_get(v_inst_818_, 1);
lean_inc(v_assertShared_824_);
v_isDebugEnabled_825_ = lean_ctor_get(v_inst_818_, 2);
lean_inc(v_isDebugEnabled_825_);
lean_dec_ref(v_inst_818_);
lean_inc_ref(v_e_821_);
v___f_826_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__0), 4, 3);
lean_closure_set(v___f_826_, 0, v_d_820_);
lean_closure_set(v___f_826_, 1, v_e_821_);
lean_closure_set(v___f_826_, 2, v_share1_823_);
lean_inc_ref(v___f_826_);
v___f_827_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_827_, 0, v___f_826_);
v___f_828_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_828_, 0, v___f_826_);
lean_closure_set(v___f_828_, 1, v_assertShared_824_);
lean_closure_set(v___f_828_, 2, v_e_821_);
lean_closure_set(v___f_828_, 3, v_toBind_822_);
lean_closure_set(v___f_828_, 4, v___f_827_);
v___x_829_ = lean_apply_4(v_toBind_822_, lean_box(0), lean_box(0), v_isDebugEnabled_825_, v___f_828_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS(lean_object* v_m_830_, lean_object* v_inst_831_, lean_object* v_inst_832_, lean_object* v_d_833_, lean_object* v_e_834_){
_start:
{
lean_object* v___x_835_; 
v___x_835_ = l_Lean_Meta_Sym_Internal_mkMDataS___redArg(v_inst_831_, v_inst_832_, v_d_833_, v_e_834_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__0(lean_object* v_structName_836_, lean_object* v_idx_837_, lean_object* v_struct_838_, lean_object* v_share1_839_, lean_object* v_____r_840_){
_start:
{
lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_841_ = l_Lean_Expr_proj___override(v_structName_836_, v_idx_837_, v_struct_838_);
v___x_842_ = lean_apply_1(v_share1_839_, v___x_841_);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__2(lean_object* v___f_843_, lean_object* v_assertShared_844_, lean_object* v_struct_845_, lean_object* v_toBind_846_, lean_object* v___f_847_, uint8_t v_____do__lift_848_){
_start:
{
if (v_____do__lift_848_ == 0)
{
lean_object* v___x_849_; lean_object* v___x_850_; 
lean_dec(v___f_847_);
lean_dec(v_toBind_846_);
lean_dec_ref(v_struct_845_);
lean_dec(v_assertShared_844_);
v___x_849_ = lean_box(0);
v___x_850_ = lean_apply_1(v___f_843_, v___x_849_);
return v___x_850_;
}
else
{
lean_object* v___x_851_; lean_object* v___x_852_; 
lean_dec(v___f_843_);
v___x_851_ = lean_apply_1(v_assertShared_844_, v_struct_845_);
v___x_852_ = lean_apply_4(v_toBind_846_, lean_box(0), lean_box(0), v___x_851_, v___f_847_);
return v___x_852_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__2___boxed(lean_object* v___f_853_, lean_object* v_assertShared_854_, lean_object* v_struct_855_, lean_object* v_toBind_856_, lean_object* v___f_857_, lean_object* v_____do__lift_858_){
_start:
{
uint8_t v_____do__lift_57__boxed_859_; lean_object* v_res_860_; 
v_____do__lift_57__boxed_859_ = lean_unbox(v_____do__lift_858_);
v_res_860_ = l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__2(v___f_853_, v_assertShared_854_, v_struct_855_, v_toBind_856_, v___f_857_, v_____do__lift_57__boxed_859_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___redArg(lean_object* v_inst_861_, lean_object* v_inst_862_, lean_object* v_structName_863_, lean_object* v_idx_864_, lean_object* v_struct_865_){
_start:
{
lean_object* v_toBind_866_; lean_object* v_share1_867_; lean_object* v_assertShared_868_; lean_object* v_isDebugEnabled_869_; lean_object* v___f_870_; lean_object* v___f_871_; lean_object* v___f_872_; lean_object* v___x_873_; 
v_toBind_866_ = lean_ctor_get(v_inst_862_, 1);
lean_inc_n(v_toBind_866_, 2);
lean_dec_ref(v_inst_862_);
v_share1_867_ = lean_ctor_get(v_inst_861_, 0);
lean_inc(v_share1_867_);
v_assertShared_868_ = lean_ctor_get(v_inst_861_, 1);
lean_inc(v_assertShared_868_);
v_isDebugEnabled_869_ = lean_ctor_get(v_inst_861_, 2);
lean_inc(v_isDebugEnabled_869_);
lean_dec_ref(v_inst_861_);
lean_inc_ref(v_struct_865_);
v___f_870_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__0), 5, 4);
lean_closure_set(v___f_870_, 0, v_structName_863_);
lean_closure_set(v___f_870_, 1, v_idx_864_);
lean_closure_set(v___f_870_, 2, v_struct_865_);
lean_closure_set(v___f_870_, 3, v_share1_867_);
lean_inc_ref(v___f_870_);
v___f_871_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_871_, 0, v___f_870_);
v___f_872_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_872_, 0, v___f_870_);
lean_closure_set(v___f_872_, 1, v_assertShared_868_);
lean_closure_set(v___f_872_, 2, v_struct_865_);
lean_closure_set(v___f_872_, 3, v_toBind_866_);
lean_closure_set(v___f_872_, 4, v___f_871_);
v___x_873_ = lean_apply_4(v_toBind_866_, lean_box(0), lean_box(0), v_isDebugEnabled_869_, v___f_872_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS(lean_object* v_m_874_, lean_object* v_inst_875_, lean_object* v_inst_876_, lean_object* v_structName_877_, lean_object* v_idx_878_, lean_object* v_struct_879_){
_start:
{
lean_object* v___x_880_; 
v___x_880_ = l_Lean_Meta_Sym_Internal_mkProjS___redArg(v_inst_875_, v_inst_876_, v_structName_877_, v_idx_878_, v_struct_879_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__0(lean_object* v_f_881_, lean_object* v_a_882_, lean_object* v_share1_883_, lean_object* v_____r_884_){
_start:
{
lean_object* v___x_885_; lean_object* v___x_886_; 
v___x_885_ = l_Lean_Expr_app___override(v_f_881_, v_a_882_);
v___x_886_ = lean_apply_1(v_share1_883_, v___x_885_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__2(lean_object* v_assertShared_887_, lean_object* v_a_888_, lean_object* v_toBind_889_, lean_object* v___f_890_, lean_object* v_____r_891_){
_start:
{
lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_892_ = lean_apply_1(v_assertShared_887_, v_a_888_);
v___x_893_ = lean_apply_4(v_toBind_889_, lean_box(0), lean_box(0), v___x_892_, v___f_890_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__1(lean_object* v___f_894_, lean_object* v_assertShared_895_, lean_object* v_a_896_, lean_object* v_toBind_897_, lean_object* v___f_898_, lean_object* v_f_899_, uint8_t v_____do__lift_900_){
_start:
{
if (v_____do__lift_900_ == 0)
{
lean_object* v___x_901_; lean_object* v___x_902_; 
lean_dec_ref(v_f_899_);
lean_dec(v___f_898_);
lean_dec(v_toBind_897_);
lean_dec_ref(v_a_896_);
lean_dec(v_assertShared_895_);
v___x_901_ = lean_box(0);
v___x_902_ = lean_apply_1(v___f_894_, v___x_901_);
return v___x_902_;
}
else
{
lean_object* v___f_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
lean_dec(v___f_894_);
lean_inc(v_toBind_897_);
lean_inc(v_assertShared_895_);
v___f_903_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__2), 5, 4);
lean_closure_set(v___f_903_, 0, v_assertShared_895_);
lean_closure_set(v___f_903_, 1, v_a_896_);
lean_closure_set(v___f_903_, 2, v_toBind_897_);
lean_closure_set(v___f_903_, 3, v___f_898_);
v___x_904_ = lean_apply_1(v_assertShared_895_, v_f_899_);
v___x_905_ = lean_apply_4(v_toBind_897_, lean_box(0), lean_box(0), v___x_904_, v___f_903_);
return v___x_905_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__1___boxed(lean_object* v___f_906_, lean_object* v_assertShared_907_, lean_object* v_a_908_, lean_object* v_toBind_909_, lean_object* v___f_910_, lean_object* v_f_911_, lean_object* v_____do__lift_912_){
_start:
{
uint8_t v_____do__lift_74__boxed_913_; lean_object* v_res_914_; 
v_____do__lift_74__boxed_913_ = lean_unbox(v_____do__lift_912_);
v_res_914_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__1(v___f_906_, v_assertShared_907_, v_a_908_, v_toBind_909_, v___f_910_, v_f_911_, v_____do__lift_74__boxed_913_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg(lean_object* v_inst_915_, lean_object* v_inst_916_, lean_object* v_f_917_, lean_object* v_a_918_){
_start:
{
lean_object* v_toBind_919_; lean_object* v_share1_920_; lean_object* v_assertShared_921_; lean_object* v_isDebugEnabled_922_; lean_object* v___f_923_; lean_object* v___f_924_; lean_object* v___f_925_; lean_object* v___x_926_; 
v_toBind_919_ = lean_ctor_get(v_inst_916_, 1);
lean_inc_n(v_toBind_919_, 2);
lean_dec_ref(v_inst_916_);
v_share1_920_ = lean_ctor_get(v_inst_915_, 0);
lean_inc(v_share1_920_);
v_assertShared_921_ = lean_ctor_get(v_inst_915_, 1);
lean_inc(v_assertShared_921_);
v_isDebugEnabled_922_ = lean_ctor_get(v_inst_915_, 2);
lean_inc(v_isDebugEnabled_922_);
lean_dec_ref(v_inst_915_);
lean_inc_ref(v_a_918_);
lean_inc_ref(v_f_917_);
v___f_923_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__0), 4, 3);
lean_closure_set(v___f_923_, 0, v_f_917_);
lean_closure_set(v___f_923_, 1, v_a_918_);
lean_closure_set(v___f_923_, 2, v_share1_920_);
lean_inc_ref(v___f_923_);
v___f_924_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_924_, 0, v___f_923_);
v___f_925_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_925_, 0, v___f_923_);
lean_closure_set(v___f_925_, 1, v_assertShared_921_);
lean_closure_set(v___f_925_, 2, v_a_918_);
lean_closure_set(v___f_925_, 3, v_toBind_919_);
lean_closure_set(v___f_925_, 4, v___f_924_);
lean_closure_set(v___f_925_, 5, v_f_917_);
v___x_926_ = lean_apply_4(v_toBind_919_, lean_box(0), lean_box(0), v_isDebugEnabled_922_, v___f_925_);
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS(lean_object* v_m_927_, lean_object* v_inst_928_, lean_object* v_inst_929_, lean_object* v_f_930_, lean_object* v_a_931_){
_start:
{
lean_object* v___x_932_; 
v___x_932_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_928_, v_inst_929_, v_f_930_, v_a_931_);
return v___x_932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__0(lean_object* v_x_933_, lean_object* v_t_934_, lean_object* v_b_935_, uint8_t v_bi_936_, lean_object* v_share1_937_, lean_object* v_____r_938_){
_start:
{
lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_939_ = l_Lean_Expr_lam___override(v_x_933_, v_t_934_, v_b_935_, v_bi_936_);
v___x_940_ = lean_apply_1(v_share1_937_, v___x_939_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__0___boxed(lean_object* v_x_941_, lean_object* v_t_942_, lean_object* v_b_943_, lean_object* v_bi_944_, lean_object* v_share1_945_, lean_object* v_____r_946_){
_start:
{
uint8_t v_bi_boxed_947_; lean_object* v_res_948_; 
v_bi_boxed_947_ = lean_unbox(v_bi_944_);
v_res_948_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__0(v_x_941_, v_t_942_, v_b_943_, v_bi_boxed_947_, v_share1_945_, v_____r_946_);
return v_res_948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__2(lean_object* v_assertShared_949_, lean_object* v_b_950_, lean_object* v_toBind_951_, lean_object* v___f_952_, lean_object* v_____r_953_){
_start:
{
lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_954_ = lean_apply_1(v_assertShared_949_, v_b_950_);
v___x_955_ = lean_apply_4(v_toBind_951_, lean_box(0), lean_box(0), v___x_954_, v___f_952_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1(lean_object* v___f_956_, lean_object* v_assertShared_957_, lean_object* v_b_958_, lean_object* v_toBind_959_, lean_object* v___f_960_, lean_object* v_t_961_, uint8_t v_____do__lift_962_){
_start:
{
if (v_____do__lift_962_ == 0)
{
lean_object* v___x_963_; lean_object* v___x_964_; 
lean_dec_ref(v_t_961_);
lean_dec(v___f_960_);
lean_dec(v_toBind_959_);
lean_dec_ref(v_b_958_);
lean_dec(v_assertShared_957_);
v___x_963_ = lean_box(0);
v___x_964_ = lean_apply_1(v___f_956_, v___x_963_);
return v___x_964_;
}
else
{
lean_object* v___f_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
lean_dec(v___f_956_);
lean_inc(v_toBind_959_);
lean_inc(v_assertShared_957_);
v___f_965_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__2), 5, 4);
lean_closure_set(v___f_965_, 0, v_assertShared_957_);
lean_closure_set(v___f_965_, 1, v_b_958_);
lean_closure_set(v___f_965_, 2, v_toBind_959_);
lean_closure_set(v___f_965_, 3, v___f_960_);
v___x_966_ = lean_apply_1(v_assertShared_957_, v_t_961_);
v___x_967_ = lean_apply_4(v_toBind_959_, lean_box(0), lean_box(0), v___x_966_, v___f_965_);
return v___x_967_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1___boxed(lean_object* v___f_968_, lean_object* v_assertShared_969_, lean_object* v_b_970_, lean_object* v_toBind_971_, lean_object* v___f_972_, lean_object* v_t_973_, lean_object* v_____do__lift_974_){
_start:
{
uint8_t v_____do__lift_75__boxed_975_; lean_object* v_res_976_; 
v_____do__lift_75__boxed_975_ = lean_unbox(v_____do__lift_974_);
v_res_976_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1(v___f_968_, v_assertShared_969_, v_b_970_, v_toBind_971_, v___f_972_, v_t_973_, v_____do__lift_75__boxed_975_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(lean_object* v_inst_977_, lean_object* v_inst_978_, lean_object* v_x_979_, uint8_t v_bi_980_, lean_object* v_t_981_, lean_object* v_b_982_){
_start:
{
lean_object* v_toBind_983_; lean_object* v_share1_984_; lean_object* v_assertShared_985_; lean_object* v_isDebugEnabled_986_; lean_object* v___x_987_; lean_object* v___f_988_; lean_object* v___f_989_; lean_object* v___f_990_; lean_object* v___x_991_; 
v_toBind_983_ = lean_ctor_get(v_inst_978_, 1);
lean_inc_n(v_toBind_983_, 2);
lean_dec_ref(v_inst_978_);
v_share1_984_ = lean_ctor_get(v_inst_977_, 0);
lean_inc(v_share1_984_);
v_assertShared_985_ = lean_ctor_get(v_inst_977_, 1);
lean_inc(v_assertShared_985_);
v_isDebugEnabled_986_ = lean_ctor_get(v_inst_977_, 2);
lean_inc(v_isDebugEnabled_986_);
lean_dec_ref(v_inst_977_);
v___x_987_ = lean_box(v_bi_980_);
lean_inc_ref(v_b_982_);
lean_inc_ref(v_t_981_);
v___f_988_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_988_, 0, v_x_979_);
lean_closure_set(v___f_988_, 1, v_t_981_);
lean_closure_set(v___f_988_, 2, v_b_982_);
lean_closure_set(v___f_988_, 3, v___x_987_);
lean_closure_set(v___f_988_, 4, v_share1_984_);
lean_inc_ref(v___f_988_);
v___f_989_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_989_, 0, v___f_988_);
v___f_990_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_990_, 0, v___f_988_);
lean_closure_set(v___f_990_, 1, v_assertShared_985_);
lean_closure_set(v___f_990_, 2, v_b_982_);
lean_closure_set(v___f_990_, 3, v_toBind_983_);
lean_closure_set(v___f_990_, 4, v___f_989_);
lean_closure_set(v___f_990_, 5, v_t_981_);
v___x_991_ = lean_apply_4(v_toBind_983_, lean_box(0), lean_box(0), v_isDebugEnabled_986_, v___f_990_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___boxed(lean_object* v_inst_992_, lean_object* v_inst_993_, lean_object* v_x_994_, lean_object* v_bi_995_, lean_object* v_t_996_, lean_object* v_b_997_){
_start:
{
uint8_t v_bi_boxed_998_; lean_object* v_res_999_; 
v_bi_boxed_998_ = lean_unbox(v_bi_995_);
v_res_999_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v_inst_992_, v_inst_993_, v_x_994_, v_bi_boxed_998_, v_t_996_, v_b_997_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS(lean_object* v_m_1000_, lean_object* v_inst_1001_, lean_object* v_inst_1002_, lean_object* v_x_1003_, uint8_t v_bi_1004_, lean_object* v_t_1005_, lean_object* v_b_1006_){
_start:
{
lean_object* v___x_1007_; 
v___x_1007_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v_inst_1001_, v_inst_1002_, v_x_1003_, v_bi_1004_, v_t_1005_, v_b_1006_);
return v___x_1007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___boxed(lean_object* v_m_1008_, lean_object* v_inst_1009_, lean_object* v_inst_1010_, lean_object* v_x_1011_, lean_object* v_bi_1012_, lean_object* v_t_1013_, lean_object* v_b_1014_){
_start:
{
uint8_t v_bi_boxed_1015_; lean_object* v_res_1016_; 
v_bi_boxed_1015_ = lean_unbox(v_bi_1012_);
v_res_1016_ = l_Lean_Meta_Sym_Internal_mkLambdaS(v_m_1008_, v_inst_1009_, v_inst_1010_, v_x_1011_, v_bi_boxed_1015_, v_t_1013_, v_b_1014_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___redArg___lam__0(lean_object* v_x_1017_, lean_object* v_t_1018_, lean_object* v_b_1019_, uint8_t v_bi_1020_, lean_object* v_share1_1021_, lean_object* v_____r_1022_){
_start:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1023_ = l_Lean_Expr_forallE___override(v_x_1017_, v_t_1018_, v_b_1019_, v_bi_1020_);
v___x_1024_ = lean_apply_1(v_share1_1021_, v___x_1023_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___redArg___lam__0___boxed(lean_object* v_x_1025_, lean_object* v_t_1026_, lean_object* v_b_1027_, lean_object* v_bi_1028_, lean_object* v_share1_1029_, lean_object* v_____r_1030_){
_start:
{
uint8_t v_bi_boxed_1031_; lean_object* v_res_1032_; 
v_bi_boxed_1031_ = lean_unbox(v_bi_1028_);
v_res_1032_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg___lam__0(v_x_1025_, v_t_1026_, v_b_1027_, v_bi_boxed_1031_, v_share1_1029_, v_____r_1030_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___redArg(lean_object* v_inst_1033_, lean_object* v_inst_1034_, lean_object* v_x_1035_, uint8_t v_bi_1036_, lean_object* v_t_1037_, lean_object* v_b_1038_){
_start:
{
lean_object* v_toBind_1039_; lean_object* v_share1_1040_; lean_object* v_assertShared_1041_; lean_object* v_isDebugEnabled_1042_; lean_object* v___x_1043_; lean_object* v___f_1044_; lean_object* v___f_1045_; lean_object* v___f_1046_; lean_object* v___x_1047_; 
v_toBind_1039_ = lean_ctor_get(v_inst_1034_, 1);
lean_inc_n(v_toBind_1039_, 2);
lean_dec_ref(v_inst_1034_);
v_share1_1040_ = lean_ctor_get(v_inst_1033_, 0);
lean_inc(v_share1_1040_);
v_assertShared_1041_ = lean_ctor_get(v_inst_1033_, 1);
lean_inc(v_assertShared_1041_);
v_isDebugEnabled_1042_ = lean_ctor_get(v_inst_1033_, 2);
lean_inc(v_isDebugEnabled_1042_);
lean_dec_ref(v_inst_1033_);
v___x_1043_ = lean_box(v_bi_1036_);
lean_inc_ref(v_b_1038_);
lean_inc_ref(v_t_1037_);
v___f_1044_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkForallS___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1044_, 0, v_x_1035_);
lean_closure_set(v___f_1044_, 1, v_t_1037_);
lean_closure_set(v___f_1044_, 2, v_b_1038_);
lean_closure_set(v___f_1044_, 3, v___x_1043_);
lean_closure_set(v___f_1044_, 4, v_share1_1040_);
lean_inc_ref(v___f_1044_);
v___f_1045_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1045_, 0, v___f_1044_);
v___f_1046_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_1046_, 0, v___f_1044_);
lean_closure_set(v___f_1046_, 1, v_assertShared_1041_);
lean_closure_set(v___f_1046_, 2, v_b_1038_);
lean_closure_set(v___f_1046_, 3, v_toBind_1039_);
lean_closure_set(v___f_1046_, 4, v___f_1045_);
lean_closure_set(v___f_1046_, 5, v_t_1037_);
v___x_1047_ = lean_apply_4(v_toBind_1039_, lean_box(0), lean_box(0), v_isDebugEnabled_1042_, v___f_1046_);
return v___x_1047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___redArg___boxed(lean_object* v_inst_1048_, lean_object* v_inst_1049_, lean_object* v_x_1050_, lean_object* v_bi_1051_, lean_object* v_t_1052_, lean_object* v_b_1053_){
_start:
{
uint8_t v_bi_boxed_1054_; lean_object* v_res_1055_; 
v_bi_boxed_1054_ = lean_unbox(v_bi_1051_);
v_res_1055_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v_inst_1048_, v_inst_1049_, v_x_1050_, v_bi_boxed_1054_, v_t_1052_, v_b_1053_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS(lean_object* v_m_1056_, lean_object* v_inst_1057_, lean_object* v_inst_1058_, lean_object* v_x_1059_, uint8_t v_bi_1060_, lean_object* v_t_1061_, lean_object* v_b_1062_){
_start:
{
lean_object* v___x_1063_; 
v___x_1063_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v_inst_1057_, v_inst_1058_, v_x_1059_, v_bi_1060_, v_t_1061_, v_b_1062_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___boxed(lean_object* v_m_1064_, lean_object* v_inst_1065_, lean_object* v_inst_1066_, lean_object* v_x_1067_, lean_object* v_bi_1068_, lean_object* v_t_1069_, lean_object* v_b_1070_){
_start:
{
uint8_t v_bi_boxed_1071_; lean_object* v_res_1072_; 
v_bi_boxed_1071_ = lean_unbox(v_bi_1068_);
v_res_1072_ = l_Lean_Meta_Sym_Internal_mkForallS(v_m_1064_, v_inst_1065_, v_inst_1066_, v_x_1067_, v_bi_boxed_1071_, v_t_1069_, v_b_1070_);
return v_res_1072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__0(lean_object* v_x_1073_, lean_object* v_t_1074_, lean_object* v_v_1075_, lean_object* v_b_1076_, uint8_t v_nondep_1077_, lean_object* v_share1_1078_, lean_object* v_____r_1079_){
_start:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; 
v___x_1080_ = l_Lean_Expr_letE___override(v_x_1073_, v_t_1074_, v_v_1075_, v_b_1076_, v_nondep_1077_);
v___x_1081_ = lean_apply_1(v_share1_1078_, v___x_1080_);
return v___x_1081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__0___boxed(lean_object* v_x_1082_, lean_object* v_t_1083_, lean_object* v_v_1084_, lean_object* v_b_1085_, lean_object* v_nondep_1086_, lean_object* v_share1_1087_, lean_object* v_____r_1088_){
_start:
{
uint8_t v_nondep_boxed_1089_; lean_object* v_res_1090_; 
v_nondep_boxed_1089_ = lean_unbox(v_nondep_1086_);
v_res_1090_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__0(v_x_1082_, v_t_1083_, v_v_1084_, v_b_1085_, v_nondep_boxed_1089_, v_share1_1087_, v_____r_1088_);
return v_res_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__3(lean_object* v_assertShared_1091_, lean_object* v_v_1092_, lean_object* v_toBind_1093_, lean_object* v___f_1094_, lean_object* v_____r_1095_){
_start:
{
lean_object* v___x_1096_; lean_object* v___x_1097_; 
v___x_1096_ = lean_apply_1(v_assertShared_1091_, v_v_1092_);
v___x_1097_ = lean_apply_4(v_toBind_1093_, lean_box(0), lean_box(0), v___x_1096_, v___f_1094_);
return v___x_1097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1(lean_object* v___f_1098_, lean_object* v_assertShared_1099_, lean_object* v_b_1100_, lean_object* v_toBind_1101_, lean_object* v___f_1102_, lean_object* v_v_1103_, lean_object* v_t_1104_, uint8_t v_____do__lift_1105_){
_start:
{
if (v_____do__lift_1105_ == 0)
{
lean_object* v___x_1106_; lean_object* v___x_1107_; 
lean_dec_ref(v_t_1104_);
lean_dec_ref(v_v_1103_);
lean_dec(v___f_1102_);
lean_dec(v_toBind_1101_);
lean_dec_ref(v_b_1100_);
lean_dec(v_assertShared_1099_);
v___x_1106_ = lean_box(0);
v___x_1107_ = lean_apply_1(v___f_1098_, v___x_1106_);
return v___x_1107_;
}
else
{
lean_object* v___f_1108_; lean_object* v___f_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
lean_dec(v___f_1098_);
lean_inc_n(v_toBind_1101_, 2);
lean_inc_n(v_assertShared_1099_, 2);
v___f_1108_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__2), 5, 4);
lean_closure_set(v___f_1108_, 0, v_assertShared_1099_);
lean_closure_set(v___f_1108_, 1, v_b_1100_);
lean_closure_set(v___f_1108_, 2, v_toBind_1101_);
lean_closure_set(v___f_1108_, 3, v___f_1102_);
v___f_1109_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__3), 5, 4);
lean_closure_set(v___f_1109_, 0, v_assertShared_1099_);
lean_closure_set(v___f_1109_, 1, v_v_1103_);
lean_closure_set(v___f_1109_, 2, v_toBind_1101_);
lean_closure_set(v___f_1109_, 3, v___f_1108_);
v___x_1110_ = lean_apply_1(v_assertShared_1099_, v_t_1104_);
v___x_1111_ = lean_apply_4(v_toBind_1101_, lean_box(0), lean_box(0), v___x_1110_, v___f_1109_);
return v___x_1111_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1___boxed(lean_object* v___f_1112_, lean_object* v_assertShared_1113_, lean_object* v_b_1114_, lean_object* v_toBind_1115_, lean_object* v___f_1116_, lean_object* v_v_1117_, lean_object* v_t_1118_, lean_object* v_____do__lift_1119_){
_start:
{
uint8_t v_____do__lift_84__boxed_1120_; lean_object* v_res_1121_; 
v_____do__lift_84__boxed_1120_ = lean_unbox(v_____do__lift_1119_);
v_res_1121_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1(v___f_1112_, v_assertShared_1113_, v_b_1114_, v_toBind_1115_, v___f_1116_, v_v_1117_, v_t_1118_, v_____do__lift_84__boxed_1120_);
return v_res_1121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg(lean_object* v_inst_1122_, lean_object* v_inst_1123_, lean_object* v_x_1124_, lean_object* v_t_1125_, lean_object* v_v_1126_, lean_object* v_b_1127_, uint8_t v_nondep_1128_){
_start:
{
lean_object* v_toBind_1129_; lean_object* v_share1_1130_; lean_object* v_assertShared_1131_; lean_object* v_isDebugEnabled_1132_; lean_object* v___x_1133_; lean_object* v___f_1134_; lean_object* v___f_1135_; lean_object* v___f_1136_; lean_object* v___x_1137_; 
v_toBind_1129_ = lean_ctor_get(v_inst_1123_, 1);
lean_inc_n(v_toBind_1129_, 2);
lean_dec_ref(v_inst_1123_);
v_share1_1130_ = lean_ctor_get(v_inst_1122_, 0);
lean_inc(v_share1_1130_);
v_assertShared_1131_ = lean_ctor_get(v_inst_1122_, 1);
lean_inc(v_assertShared_1131_);
v_isDebugEnabled_1132_ = lean_ctor_get(v_inst_1122_, 2);
lean_inc(v_isDebugEnabled_1132_);
lean_dec_ref(v_inst_1122_);
v___x_1133_ = lean_box(v_nondep_1128_);
lean_inc_ref(v_b_1127_);
lean_inc_ref(v_v_1126_);
lean_inc_ref(v_t_1125_);
v___f_1134_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_1134_, 0, v_x_1124_);
lean_closure_set(v___f_1134_, 1, v_t_1125_);
lean_closure_set(v___f_1134_, 2, v_v_1126_);
lean_closure_set(v___f_1134_, 3, v_b_1127_);
lean_closure_set(v___f_1134_, 4, v___x_1133_);
lean_closure_set(v___f_1134_, 5, v_share1_1130_);
lean_inc_ref(v___f_1134_);
v___f_1135_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1135_, 0, v___f_1134_);
v___f_1136_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_1136_, 0, v___f_1134_);
lean_closure_set(v___f_1136_, 1, v_assertShared_1131_);
lean_closure_set(v___f_1136_, 2, v_b_1127_);
lean_closure_set(v___f_1136_, 3, v_toBind_1129_);
lean_closure_set(v___f_1136_, 4, v___f_1135_);
lean_closure_set(v___f_1136_, 5, v_v_1126_);
lean_closure_set(v___f_1136_, 6, v_t_1125_);
v___x_1137_ = lean_apply_4(v_toBind_1129_, lean_box(0), lean_box(0), v_isDebugEnabled_1132_, v___f_1136_);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___boxed(lean_object* v_inst_1138_, lean_object* v_inst_1139_, lean_object* v_x_1140_, lean_object* v_t_1141_, lean_object* v_v_1142_, lean_object* v_b_1143_, lean_object* v_nondep_1144_){
_start:
{
uint8_t v_nondep_boxed_1145_; lean_object* v_res_1146_; 
v_nondep_boxed_1145_ = lean_unbox(v_nondep_1144_);
v_res_1146_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1138_, v_inst_1139_, v_x_1140_, v_t_1141_, v_v_1142_, v_b_1143_, v_nondep_boxed_1145_);
return v_res_1146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS(lean_object* v_m_1147_, lean_object* v_inst_1148_, lean_object* v_inst_1149_, lean_object* v_x_1150_, lean_object* v_t_1151_, lean_object* v_v_1152_, lean_object* v_b_1153_, uint8_t v_nondep_1154_){
_start:
{
lean_object* v___x_1155_; 
v___x_1155_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1148_, v_inst_1149_, v_x_1150_, v_t_1151_, v_v_1152_, v_b_1153_, v_nondep_1154_);
return v___x_1155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___boxed(lean_object* v_m_1156_, lean_object* v_inst_1157_, lean_object* v_inst_1158_, lean_object* v_x_1159_, lean_object* v_t_1160_, lean_object* v_v_1161_, lean_object* v_b_1162_, lean_object* v_nondep_1163_){
_start:
{
uint8_t v_nondep_boxed_1164_; lean_object* v_res_1165_; 
v_nondep_boxed_1164_ = lean_unbox(v_nondep_1163_);
v_res_1165_ = l_Lean_Meta_Sym_Internal_mkLetS(v_m_1156_, v_inst_1157_, v_inst_1158_, v_x_1159_, v_t_1160_, v_v_1161_, v_b_1162_, v_nondep_boxed_1164_);
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkHaveS___redArg___lam__0(lean_object* v_x_1166_, lean_object* v_t_1167_, lean_object* v_v_1168_, lean_object* v_b_1169_, lean_object* v_share1_1170_, lean_object* v_____r_1171_){
_start:
{
uint8_t v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1172_ = 1;
v___x_1173_ = l_Lean_Expr_letE___override(v_x_1166_, v_t_1167_, v_v_1168_, v_b_1169_, v___x_1172_);
v___x_1174_ = lean_apply_1(v_share1_1170_, v___x_1173_);
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkHaveS___redArg(lean_object* v_inst_1175_, lean_object* v_inst_1176_, lean_object* v_x_1177_, lean_object* v_t_1178_, lean_object* v_v_1179_, lean_object* v_b_1180_){
_start:
{
lean_object* v_toBind_1181_; lean_object* v_share1_1182_; lean_object* v_assertShared_1183_; lean_object* v_isDebugEnabled_1184_; lean_object* v___f_1185_; lean_object* v___f_1186_; lean_object* v___f_1187_; lean_object* v___x_1188_; 
v_toBind_1181_ = lean_ctor_get(v_inst_1176_, 1);
lean_inc_n(v_toBind_1181_, 2);
lean_dec_ref(v_inst_1176_);
v_share1_1182_ = lean_ctor_get(v_inst_1175_, 0);
lean_inc(v_share1_1182_);
v_assertShared_1183_ = lean_ctor_get(v_inst_1175_, 1);
lean_inc(v_assertShared_1183_);
v_isDebugEnabled_1184_ = lean_ctor_get(v_inst_1175_, 2);
lean_inc(v_isDebugEnabled_1184_);
lean_dec_ref(v_inst_1175_);
lean_inc_ref(v_b_1180_);
lean_inc_ref(v_v_1179_);
lean_inc_ref(v_t_1178_);
v___f_1185_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkHaveS___redArg___lam__0), 6, 5);
lean_closure_set(v___f_1185_, 0, v_x_1177_);
lean_closure_set(v___f_1185_, 1, v_t_1178_);
lean_closure_set(v___f_1185_, 2, v_v_1179_);
lean_closure_set(v___f_1185_, 3, v_b_1180_);
lean_closure_set(v___f_1185_, 4, v_share1_1182_);
lean_inc_ref(v___f_1185_);
v___f_1186_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1186_, 0, v___f_1185_);
v___f_1187_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_1187_, 0, v___f_1185_);
lean_closure_set(v___f_1187_, 1, v_assertShared_1183_);
lean_closure_set(v___f_1187_, 2, v_b_1180_);
lean_closure_set(v___f_1187_, 3, v_toBind_1181_);
lean_closure_set(v___f_1187_, 4, v___f_1186_);
lean_closure_set(v___f_1187_, 5, v_v_1179_);
lean_closure_set(v___f_1187_, 6, v_t_1178_);
v___x_1188_ = lean_apply_4(v_toBind_1181_, lean_box(0), lean_box(0), v_isDebugEnabled_1184_, v___f_1187_);
return v___x_1188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkHaveS(lean_object* v_m_1189_, lean_object* v_inst_1190_, lean_object* v_inst_1191_, lean_object* v_x_1192_, lean_object* v_t_1193_, lean_object* v_v_1194_, lean_object* v_b_1195_){
_start:
{
lean_object* v___x_1196_; 
v___x_1196_ = l_Lean_Meta_Sym_Internal_mkHaveS___redArg(v_inst_1190_, v_inst_1191_, v_x_1192_, v_t_1193_, v_v_1194_, v_b_1195_);
return v___x_1196_;
}
}
static lean_object* _init_l_Lean_Expr_updateAppS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; 
v___x_1199_ = ((lean_object*)(l_Lean_Expr_updateAppS_x21___redArg___closed__1));
v___x_1200_ = lean_unsigned_to_nat(25u);
v___x_1201_ = lean_unsigned_to_nat(148u);
v___x_1202_ = ((lean_object*)(l_Lean_Expr_updateAppS_x21___redArg___closed__0));
v___x_1203_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1204_ = l_mkPanicMessageWithDecl(v___x_1203_, v___x_1202_, v___x_1201_, v___x_1200_, v___x_1199_);
return v___x_1204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateAppS_x21___redArg(lean_object* v_inst_1205_, lean_object* v_inst_1206_, lean_object* v_e_1207_, lean_object* v_newFn_1208_, lean_object* v_newArg_1209_){
_start:
{
if (lean_obj_tag(v_e_1207_) == 5)
{
lean_object* v_toApplicative_1210_; lean_object* v_toPure_1211_; lean_object* v_fn_1212_; lean_object* v_arg_1213_; size_t v___x_1214_; size_t v___x_1215_; uint8_t v___x_1216_; 
v_toApplicative_1210_ = lean_ctor_get(v_inst_1206_, 0);
v_toPure_1211_ = lean_ctor_get(v_toApplicative_1210_, 1);
v_fn_1212_ = lean_ctor_get(v_e_1207_, 0);
v_arg_1213_ = lean_ctor_get(v_e_1207_, 1);
v___x_1214_ = lean_ptr_addr(v_fn_1212_);
v___x_1215_ = lean_ptr_addr(v_newFn_1208_);
v___x_1216_ = lean_usize_dec_eq(v___x_1214_, v___x_1215_);
if (v___x_1216_ == 0)
{
lean_object* v___x_1217_; 
lean_dec_ref_known(v_e_1207_, 2);
v___x_1217_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1205_, v_inst_1206_, v_newFn_1208_, v_newArg_1209_);
return v___x_1217_;
}
else
{
size_t v___x_1218_; size_t v___x_1219_; uint8_t v___x_1220_; 
v___x_1218_ = lean_ptr_addr(v_arg_1213_);
v___x_1219_ = lean_ptr_addr(v_newArg_1209_);
v___x_1220_ = lean_usize_dec_eq(v___x_1218_, v___x_1219_);
if (v___x_1220_ == 0)
{
lean_object* v___x_1221_; 
lean_dec_ref_known(v_e_1207_, 2);
v___x_1221_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1205_, v_inst_1206_, v_newFn_1208_, v_newArg_1209_);
return v___x_1221_;
}
else
{
lean_object* v___x_1222_; 
lean_inc(v_toPure_1211_);
lean_dec_ref(v_newArg_1209_);
lean_dec_ref(v_newFn_1208_);
lean_dec_ref(v_inst_1206_);
lean_dec_ref(v_inst_1205_);
v___x_1222_ = lean_apply_2(v_toPure_1211_, lean_box(0), v_e_1207_);
return v___x_1222_;
}
}
}
else
{
lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; 
lean_dec_ref(v_newArg_1209_);
lean_dec_ref(v_newFn_1208_);
lean_dec_ref(v_e_1207_);
lean_dec_ref(v_inst_1205_);
v___x_1223_ = l_Lean_instInhabitedExpr;
v___x_1224_ = l_instInhabitedOfMonad___redArg(v_inst_1206_, v___x_1223_);
v___x_1225_ = lean_obj_once(&l_Lean_Expr_updateAppS_x21___redArg___closed__2, &l_Lean_Expr_updateAppS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateAppS_x21___redArg___closed__2);
v___x_1226_ = l_panic___redArg(v___x_1224_, v___x_1225_);
lean_dec(v___x_1224_);
return v___x_1226_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateAppS_x21(lean_object* v_m_1227_, lean_object* v_inst_1228_, lean_object* v_inst_1229_, lean_object* v_e_1230_, lean_object* v_newFn_1231_, lean_object* v_newArg_1232_){
_start:
{
if (lean_obj_tag(v_e_1230_) == 5)
{
lean_object* v_toApplicative_1233_; lean_object* v_toPure_1234_; lean_object* v_fn_1235_; lean_object* v_arg_1236_; size_t v___x_1237_; size_t v___x_1238_; uint8_t v___x_1239_; 
v_toApplicative_1233_ = lean_ctor_get(v_inst_1229_, 0);
v_toPure_1234_ = lean_ctor_get(v_toApplicative_1233_, 1);
v_fn_1235_ = lean_ctor_get(v_e_1230_, 0);
v_arg_1236_ = lean_ctor_get(v_e_1230_, 1);
v___x_1237_ = lean_ptr_addr(v_fn_1235_);
v___x_1238_ = lean_ptr_addr(v_newFn_1231_);
v___x_1239_ = lean_usize_dec_eq(v___x_1237_, v___x_1238_);
if (v___x_1239_ == 0)
{
lean_object* v___x_1240_; 
lean_dec_ref_known(v_e_1230_, 2);
v___x_1240_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1228_, v_inst_1229_, v_newFn_1231_, v_newArg_1232_);
return v___x_1240_;
}
else
{
size_t v___x_1241_; size_t v___x_1242_; uint8_t v___x_1243_; 
v___x_1241_ = lean_ptr_addr(v_arg_1236_);
v___x_1242_ = lean_ptr_addr(v_newArg_1232_);
v___x_1243_ = lean_usize_dec_eq(v___x_1241_, v___x_1242_);
if (v___x_1243_ == 0)
{
lean_object* v___x_1244_; 
lean_dec_ref_known(v_e_1230_, 2);
v___x_1244_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1228_, v_inst_1229_, v_newFn_1231_, v_newArg_1232_);
return v___x_1244_;
}
else
{
lean_object* v___x_1245_; 
lean_inc(v_toPure_1234_);
lean_dec_ref(v_newArg_1232_);
lean_dec_ref(v_newFn_1231_);
lean_dec_ref(v_inst_1229_);
lean_dec_ref(v_inst_1228_);
v___x_1245_ = lean_apply_2(v_toPure_1234_, lean_box(0), v_e_1230_);
return v___x_1245_;
}
}
}
else
{
lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; 
lean_dec_ref(v_newArg_1232_);
lean_dec_ref(v_newFn_1231_);
lean_dec_ref(v_e_1230_);
lean_dec_ref(v_inst_1228_);
v___x_1246_ = l_Lean_instInhabitedExpr;
v___x_1247_ = l_instInhabitedOfMonad___redArg(v_inst_1229_, v___x_1246_);
v___x_1248_ = lean_obj_once(&l_Lean_Expr_updateAppS_x21___redArg___closed__2, &l_Lean_Expr_updateAppS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateAppS_x21___redArg___closed__2);
v___x_1249_ = l_panic___redArg(v___x_1247_, v___x_1248_);
lean_dec(v___x_1247_);
return v___x_1249_;
}
}
}
static lean_object* _init_l_Lean_Expr_updateMDataS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; 
v___x_1252_ = ((lean_object*)(l_Lean_Expr_updateMDataS_x21___redArg___closed__1));
v___x_1253_ = lean_unsigned_to_nat(24u);
v___x_1254_ = lean_unsigned_to_nat(152u);
v___x_1255_ = ((lean_object*)(l_Lean_Expr_updateMDataS_x21___redArg___closed__0));
v___x_1256_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1257_ = l_mkPanicMessageWithDecl(v___x_1256_, v___x_1255_, v___x_1254_, v___x_1253_, v___x_1252_);
return v___x_1257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateMDataS_x21___redArg(lean_object* v_inst_1258_, lean_object* v_inst_1259_, lean_object* v_e_1260_, lean_object* v_newExpr_1261_){
_start:
{
if (lean_obj_tag(v_e_1260_) == 10)
{
lean_object* v_toApplicative_1262_; lean_object* v_toPure_1263_; lean_object* v_data_1264_; lean_object* v_expr_1265_; size_t v___x_1266_; size_t v___x_1267_; uint8_t v___x_1268_; 
v_toApplicative_1262_ = lean_ctor_get(v_inst_1259_, 0);
v_toPure_1263_ = lean_ctor_get(v_toApplicative_1262_, 1);
v_data_1264_ = lean_ctor_get(v_e_1260_, 0);
v_expr_1265_ = lean_ctor_get(v_e_1260_, 1);
v___x_1266_ = lean_ptr_addr(v_expr_1265_);
v___x_1267_ = lean_ptr_addr(v_newExpr_1261_);
v___x_1268_ = lean_usize_dec_eq(v___x_1266_, v___x_1267_);
if (v___x_1268_ == 0)
{
lean_object* v___x_1269_; 
lean_inc(v_data_1264_);
lean_dec_ref_known(v_e_1260_, 2);
v___x_1269_ = l_Lean_Meta_Sym_Internal_mkMDataS___redArg(v_inst_1258_, v_inst_1259_, v_data_1264_, v_newExpr_1261_);
return v___x_1269_;
}
else
{
lean_object* v___x_1270_; 
lean_inc(v_toPure_1263_);
lean_dec_ref(v_newExpr_1261_);
lean_dec_ref(v_inst_1259_);
lean_dec_ref(v_inst_1258_);
v___x_1270_ = lean_apply_2(v_toPure_1263_, lean_box(0), v_e_1260_);
return v___x_1270_;
}
}
else
{
lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; 
lean_dec_ref(v_newExpr_1261_);
lean_dec_ref(v_e_1260_);
lean_dec_ref(v_inst_1258_);
v___x_1271_ = l_Lean_instInhabitedExpr;
v___x_1272_ = l_instInhabitedOfMonad___redArg(v_inst_1259_, v___x_1271_);
v___x_1273_ = lean_obj_once(&l_Lean_Expr_updateMDataS_x21___redArg___closed__2, &l_Lean_Expr_updateMDataS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateMDataS_x21___redArg___closed__2);
v___x_1274_ = l_panic___redArg(v___x_1272_, v___x_1273_);
lean_dec(v___x_1272_);
return v___x_1274_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateMDataS_x21(lean_object* v_m_1275_, lean_object* v_inst_1276_, lean_object* v_inst_1277_, lean_object* v_e_1278_, lean_object* v_newExpr_1279_){
_start:
{
if (lean_obj_tag(v_e_1278_) == 10)
{
lean_object* v_toApplicative_1280_; lean_object* v_toPure_1281_; lean_object* v_data_1282_; lean_object* v_expr_1283_; size_t v___x_1284_; size_t v___x_1285_; uint8_t v___x_1286_; 
v_toApplicative_1280_ = lean_ctor_get(v_inst_1277_, 0);
v_toPure_1281_ = lean_ctor_get(v_toApplicative_1280_, 1);
v_data_1282_ = lean_ctor_get(v_e_1278_, 0);
v_expr_1283_ = lean_ctor_get(v_e_1278_, 1);
v___x_1284_ = lean_ptr_addr(v_expr_1283_);
v___x_1285_ = lean_ptr_addr(v_newExpr_1279_);
v___x_1286_ = lean_usize_dec_eq(v___x_1284_, v___x_1285_);
if (v___x_1286_ == 0)
{
lean_object* v___x_1287_; 
lean_inc(v_data_1282_);
lean_dec_ref_known(v_e_1278_, 2);
v___x_1287_ = l_Lean_Meta_Sym_Internal_mkMDataS___redArg(v_inst_1276_, v_inst_1277_, v_data_1282_, v_newExpr_1279_);
return v___x_1287_;
}
else
{
lean_object* v___x_1288_; 
lean_inc(v_toPure_1281_);
lean_dec_ref(v_newExpr_1279_);
lean_dec_ref(v_inst_1277_);
lean_dec_ref(v_inst_1276_);
v___x_1288_ = lean_apply_2(v_toPure_1281_, lean_box(0), v_e_1278_);
return v___x_1288_;
}
}
else
{
lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; 
lean_dec_ref(v_newExpr_1279_);
lean_dec_ref(v_e_1278_);
lean_dec_ref(v_inst_1276_);
v___x_1289_ = l_Lean_instInhabitedExpr;
v___x_1290_ = l_instInhabitedOfMonad___redArg(v_inst_1277_, v___x_1289_);
v___x_1291_ = lean_obj_once(&l_Lean_Expr_updateMDataS_x21___redArg___closed__2, &l_Lean_Expr_updateMDataS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateMDataS_x21___redArg___closed__2);
v___x_1292_ = l_panic___redArg(v___x_1290_, v___x_1291_);
lean_dec(v___x_1290_);
return v___x_1292_;
}
}
}
static lean_object* _init_l_Lean_Expr_updateProjS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1295_ = ((lean_object*)(l_Lean_Expr_updateProjS_x21___redArg___closed__1));
v___x_1296_ = lean_unsigned_to_nat(25u);
v___x_1297_ = lean_unsigned_to_nat(156u);
v___x_1298_ = ((lean_object*)(l_Lean_Expr_updateProjS_x21___redArg___closed__0));
v___x_1299_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1300_ = l_mkPanicMessageWithDecl(v___x_1299_, v___x_1298_, v___x_1297_, v___x_1296_, v___x_1295_);
return v___x_1300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateProjS_x21___redArg(lean_object* v_inst_1301_, lean_object* v_inst_1302_, lean_object* v_e_1303_, lean_object* v_newExpr_1304_){
_start:
{
if (lean_obj_tag(v_e_1303_) == 11)
{
lean_object* v_toApplicative_1305_; lean_object* v_toPure_1306_; lean_object* v_typeName_1307_; lean_object* v_idx_1308_; lean_object* v_struct_1309_; size_t v___x_1310_; size_t v___x_1311_; uint8_t v___x_1312_; 
v_toApplicative_1305_ = lean_ctor_get(v_inst_1302_, 0);
v_toPure_1306_ = lean_ctor_get(v_toApplicative_1305_, 1);
v_typeName_1307_ = lean_ctor_get(v_e_1303_, 0);
v_idx_1308_ = lean_ctor_get(v_e_1303_, 1);
v_struct_1309_ = lean_ctor_get(v_e_1303_, 2);
v___x_1310_ = lean_ptr_addr(v_struct_1309_);
v___x_1311_ = lean_ptr_addr(v_newExpr_1304_);
v___x_1312_ = lean_usize_dec_eq(v___x_1310_, v___x_1311_);
if (v___x_1312_ == 0)
{
lean_object* v___x_1313_; 
lean_inc(v_idx_1308_);
lean_inc(v_typeName_1307_);
lean_dec_ref_known(v_e_1303_, 3);
v___x_1313_ = l_Lean_Meta_Sym_Internal_mkProjS___redArg(v_inst_1301_, v_inst_1302_, v_typeName_1307_, v_idx_1308_, v_newExpr_1304_);
return v___x_1313_;
}
else
{
lean_object* v___x_1314_; 
lean_inc(v_toPure_1306_);
lean_dec_ref(v_newExpr_1304_);
lean_dec_ref(v_inst_1302_);
lean_dec_ref(v_inst_1301_);
v___x_1314_ = lean_apply_2(v_toPure_1306_, lean_box(0), v_e_1303_);
return v___x_1314_;
}
}
else
{
lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; 
lean_dec_ref(v_newExpr_1304_);
lean_dec_ref(v_e_1303_);
lean_dec_ref(v_inst_1301_);
v___x_1315_ = l_Lean_instInhabitedExpr;
v___x_1316_ = l_instInhabitedOfMonad___redArg(v_inst_1302_, v___x_1315_);
v___x_1317_ = lean_obj_once(&l_Lean_Expr_updateProjS_x21___redArg___closed__2, &l_Lean_Expr_updateProjS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateProjS_x21___redArg___closed__2);
v___x_1318_ = l_panic___redArg(v___x_1316_, v___x_1317_);
lean_dec(v___x_1316_);
return v___x_1318_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateProjS_x21(lean_object* v_m_1319_, lean_object* v_inst_1320_, lean_object* v_inst_1321_, lean_object* v_e_1322_, lean_object* v_newExpr_1323_){
_start:
{
if (lean_obj_tag(v_e_1322_) == 11)
{
lean_object* v_toApplicative_1324_; lean_object* v_toPure_1325_; lean_object* v_typeName_1326_; lean_object* v_idx_1327_; lean_object* v_struct_1328_; size_t v___x_1329_; size_t v___x_1330_; uint8_t v___x_1331_; 
v_toApplicative_1324_ = lean_ctor_get(v_inst_1321_, 0);
v_toPure_1325_ = lean_ctor_get(v_toApplicative_1324_, 1);
v_typeName_1326_ = lean_ctor_get(v_e_1322_, 0);
v_idx_1327_ = lean_ctor_get(v_e_1322_, 1);
v_struct_1328_ = lean_ctor_get(v_e_1322_, 2);
v___x_1329_ = lean_ptr_addr(v_struct_1328_);
v___x_1330_ = lean_ptr_addr(v_newExpr_1323_);
v___x_1331_ = lean_usize_dec_eq(v___x_1329_, v___x_1330_);
if (v___x_1331_ == 0)
{
lean_object* v___x_1332_; 
lean_inc(v_idx_1327_);
lean_inc(v_typeName_1326_);
lean_dec_ref_known(v_e_1322_, 3);
v___x_1332_ = l_Lean_Meta_Sym_Internal_mkProjS___redArg(v_inst_1320_, v_inst_1321_, v_typeName_1326_, v_idx_1327_, v_newExpr_1323_);
return v___x_1332_;
}
else
{
lean_object* v___x_1333_; 
lean_inc(v_toPure_1325_);
lean_dec_ref(v_newExpr_1323_);
lean_dec_ref(v_inst_1321_);
lean_dec_ref(v_inst_1320_);
v___x_1333_ = lean_apply_2(v_toPure_1325_, lean_box(0), v_e_1322_);
return v___x_1333_;
}
}
else
{
lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; 
lean_dec_ref(v_newExpr_1323_);
lean_dec_ref(v_e_1322_);
lean_dec_ref(v_inst_1320_);
v___x_1334_ = l_Lean_instInhabitedExpr;
v___x_1335_ = l_instInhabitedOfMonad___redArg(v_inst_1321_, v___x_1334_);
v___x_1336_ = lean_obj_once(&l_Lean_Expr_updateProjS_x21___redArg___closed__2, &l_Lean_Expr_updateProjS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateProjS_x21___redArg___closed__2);
v___x_1337_ = l_panic___redArg(v___x_1335_, v___x_1336_);
lean_dec(v___x_1335_);
return v___x_1337_;
}
}
}
static lean_object* _init_l_Lean_Expr_updateForallS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; 
v___x_1340_ = ((lean_object*)(l_Lean_Expr_updateForallS_x21___redArg___closed__1));
v___x_1341_ = lean_unsigned_to_nat(31u);
v___x_1342_ = lean_unsigned_to_nat(160u);
v___x_1343_ = ((lean_object*)(l_Lean_Expr_updateForallS_x21___redArg___closed__0));
v___x_1344_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1345_ = l_mkPanicMessageWithDecl(v___x_1344_, v___x_1343_, v___x_1342_, v___x_1341_, v___x_1340_);
return v___x_1345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallS_x21___redArg(lean_object* v_inst_1346_, lean_object* v_inst_1347_, lean_object* v_e_1348_, lean_object* v_newDomain_1349_, lean_object* v_newBody_1350_){
_start:
{
if (lean_obj_tag(v_e_1348_) == 7)
{
lean_object* v_toApplicative_1351_; lean_object* v_toPure_1352_; lean_object* v_binderName_1353_; lean_object* v_binderType_1354_; lean_object* v_body_1355_; uint8_t v_binderInfo_1356_; size_t v___x_1357_; size_t v___x_1358_; uint8_t v___x_1359_; 
v_toApplicative_1351_ = lean_ctor_get(v_inst_1347_, 0);
v_toPure_1352_ = lean_ctor_get(v_toApplicative_1351_, 1);
v_binderName_1353_ = lean_ctor_get(v_e_1348_, 0);
v_binderType_1354_ = lean_ctor_get(v_e_1348_, 1);
v_body_1355_ = lean_ctor_get(v_e_1348_, 2);
v_binderInfo_1356_ = lean_ctor_get_uint8(v_e_1348_, sizeof(void*)*3 + 8);
v___x_1357_ = lean_ptr_addr(v_binderType_1354_);
v___x_1358_ = lean_ptr_addr(v_newDomain_1349_);
v___x_1359_ = lean_usize_dec_eq(v___x_1357_, v___x_1358_);
if (v___x_1359_ == 0)
{
lean_object* v___x_1360_; 
lean_inc(v_binderName_1353_);
lean_dec_ref_known(v_e_1348_, 3);
v___x_1360_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v_inst_1346_, v_inst_1347_, v_binderName_1353_, v_binderInfo_1356_, v_newDomain_1349_, v_newBody_1350_);
return v___x_1360_;
}
else
{
size_t v___x_1361_; size_t v___x_1362_; uint8_t v___x_1363_; 
v___x_1361_ = lean_ptr_addr(v_body_1355_);
v___x_1362_ = lean_ptr_addr(v_newBody_1350_);
v___x_1363_ = lean_usize_dec_eq(v___x_1361_, v___x_1362_);
if (v___x_1363_ == 0)
{
lean_object* v___x_1364_; 
lean_inc(v_binderName_1353_);
lean_dec_ref_known(v_e_1348_, 3);
v___x_1364_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v_inst_1346_, v_inst_1347_, v_binderName_1353_, v_binderInfo_1356_, v_newDomain_1349_, v_newBody_1350_);
return v___x_1364_;
}
else
{
lean_object* v___x_1365_; 
lean_inc(v_toPure_1352_);
lean_dec_ref(v_newBody_1350_);
lean_dec_ref(v_newDomain_1349_);
lean_dec_ref(v_inst_1347_);
lean_dec_ref(v_inst_1346_);
v___x_1365_ = lean_apply_2(v_toPure_1352_, lean_box(0), v_e_1348_);
return v___x_1365_;
}
}
}
else
{
lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; 
lean_dec_ref(v_newBody_1350_);
lean_dec_ref(v_newDomain_1349_);
lean_dec_ref(v_e_1348_);
lean_dec_ref(v_inst_1346_);
v___x_1366_ = l_Lean_instInhabitedExpr;
v___x_1367_ = l_instInhabitedOfMonad___redArg(v_inst_1347_, v___x_1366_);
v___x_1368_ = lean_obj_once(&l_Lean_Expr_updateForallS_x21___redArg___closed__2, &l_Lean_Expr_updateForallS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateForallS_x21___redArg___closed__2);
v___x_1369_ = l_panic___redArg(v___x_1367_, v___x_1368_);
lean_dec(v___x_1367_);
return v___x_1369_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallS_x21(lean_object* v_m_1370_, lean_object* v_inst_1371_, lean_object* v_inst_1372_, lean_object* v_e_1373_, lean_object* v_newDomain_1374_, lean_object* v_newBody_1375_){
_start:
{
if (lean_obj_tag(v_e_1373_) == 7)
{
lean_object* v_toApplicative_1376_; lean_object* v_toPure_1377_; lean_object* v_binderName_1378_; lean_object* v_binderType_1379_; lean_object* v_body_1380_; uint8_t v_binderInfo_1381_; size_t v___x_1382_; size_t v___x_1383_; uint8_t v___x_1384_; 
v_toApplicative_1376_ = lean_ctor_get(v_inst_1372_, 0);
v_toPure_1377_ = lean_ctor_get(v_toApplicative_1376_, 1);
v_binderName_1378_ = lean_ctor_get(v_e_1373_, 0);
v_binderType_1379_ = lean_ctor_get(v_e_1373_, 1);
v_body_1380_ = lean_ctor_get(v_e_1373_, 2);
v_binderInfo_1381_ = lean_ctor_get_uint8(v_e_1373_, sizeof(void*)*3 + 8);
v___x_1382_ = lean_ptr_addr(v_binderType_1379_);
v___x_1383_ = lean_ptr_addr(v_newDomain_1374_);
v___x_1384_ = lean_usize_dec_eq(v___x_1382_, v___x_1383_);
if (v___x_1384_ == 0)
{
lean_object* v___x_1385_; 
lean_inc(v_binderName_1378_);
lean_dec_ref_known(v_e_1373_, 3);
v___x_1385_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v_inst_1371_, v_inst_1372_, v_binderName_1378_, v_binderInfo_1381_, v_newDomain_1374_, v_newBody_1375_);
return v___x_1385_;
}
else
{
size_t v___x_1386_; size_t v___x_1387_; uint8_t v___x_1388_; 
v___x_1386_ = lean_ptr_addr(v_body_1380_);
v___x_1387_ = lean_ptr_addr(v_newBody_1375_);
v___x_1388_ = lean_usize_dec_eq(v___x_1386_, v___x_1387_);
if (v___x_1388_ == 0)
{
lean_object* v___x_1389_; 
lean_inc(v_binderName_1378_);
lean_dec_ref_known(v_e_1373_, 3);
v___x_1389_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v_inst_1371_, v_inst_1372_, v_binderName_1378_, v_binderInfo_1381_, v_newDomain_1374_, v_newBody_1375_);
return v___x_1389_;
}
else
{
lean_object* v___x_1390_; 
lean_inc(v_toPure_1377_);
lean_dec_ref(v_newBody_1375_);
lean_dec_ref(v_newDomain_1374_);
lean_dec_ref(v_inst_1372_);
lean_dec_ref(v_inst_1371_);
v___x_1390_ = lean_apply_2(v_toPure_1377_, lean_box(0), v_e_1373_);
return v___x_1390_;
}
}
}
else
{
lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; 
lean_dec_ref(v_newBody_1375_);
lean_dec_ref(v_newDomain_1374_);
lean_dec_ref(v_e_1373_);
lean_dec_ref(v_inst_1371_);
v___x_1391_ = l_Lean_instInhabitedExpr;
v___x_1392_ = l_instInhabitedOfMonad___redArg(v_inst_1372_, v___x_1391_);
v___x_1393_ = lean_obj_once(&l_Lean_Expr_updateForallS_x21___redArg___closed__2, &l_Lean_Expr_updateForallS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateForallS_x21___redArg___closed__2);
v___x_1394_ = l_panic___redArg(v___x_1392_, v___x_1393_);
lean_dec(v___x_1392_);
return v___x_1394_;
}
}
}
static lean_object* _init_l_Lean_Expr_updateLambdaS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; 
v___x_1397_ = ((lean_object*)(l_Lean_Expr_updateLambdaS_x21___redArg___closed__1));
v___x_1398_ = lean_unsigned_to_nat(27u);
v___x_1399_ = lean_unsigned_to_nat(167u);
v___x_1400_ = ((lean_object*)(l_Lean_Expr_updateLambdaS_x21___redArg___closed__0));
v___x_1401_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1402_ = l_mkPanicMessageWithDecl(v___x_1401_, v___x_1400_, v___x_1399_, v___x_1398_, v___x_1397_);
return v___x_1402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLambdaS_x21___redArg(lean_object* v_inst_1403_, lean_object* v_inst_1404_, lean_object* v_e_1405_, lean_object* v_newDomain_1406_, lean_object* v_newBody_1407_){
_start:
{
if (lean_obj_tag(v_e_1405_) == 6)
{
lean_object* v_toApplicative_1408_; lean_object* v_toPure_1409_; lean_object* v_binderName_1410_; lean_object* v_binderType_1411_; lean_object* v_body_1412_; uint8_t v_binderInfo_1413_; size_t v___x_1414_; size_t v___x_1415_; uint8_t v___x_1416_; 
v_toApplicative_1408_ = lean_ctor_get(v_inst_1404_, 0);
v_toPure_1409_ = lean_ctor_get(v_toApplicative_1408_, 1);
v_binderName_1410_ = lean_ctor_get(v_e_1405_, 0);
v_binderType_1411_ = lean_ctor_get(v_e_1405_, 1);
v_body_1412_ = lean_ctor_get(v_e_1405_, 2);
v_binderInfo_1413_ = lean_ctor_get_uint8(v_e_1405_, sizeof(void*)*3 + 8);
v___x_1414_ = lean_ptr_addr(v_binderType_1411_);
v___x_1415_ = lean_ptr_addr(v_newDomain_1406_);
v___x_1416_ = lean_usize_dec_eq(v___x_1414_, v___x_1415_);
if (v___x_1416_ == 0)
{
lean_object* v___x_1417_; 
lean_inc(v_binderName_1410_);
lean_dec_ref_known(v_e_1405_, 3);
v___x_1417_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v_inst_1403_, v_inst_1404_, v_binderName_1410_, v_binderInfo_1413_, v_newDomain_1406_, v_newBody_1407_);
return v___x_1417_;
}
else
{
size_t v___x_1418_; size_t v___x_1419_; uint8_t v___x_1420_; 
v___x_1418_ = lean_ptr_addr(v_body_1412_);
v___x_1419_ = lean_ptr_addr(v_newBody_1407_);
v___x_1420_ = lean_usize_dec_eq(v___x_1418_, v___x_1419_);
if (v___x_1420_ == 0)
{
lean_object* v___x_1421_; 
lean_inc(v_binderName_1410_);
lean_dec_ref_known(v_e_1405_, 3);
v___x_1421_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v_inst_1403_, v_inst_1404_, v_binderName_1410_, v_binderInfo_1413_, v_newDomain_1406_, v_newBody_1407_);
return v___x_1421_;
}
else
{
lean_object* v___x_1422_; 
lean_inc(v_toPure_1409_);
lean_dec_ref(v_newBody_1407_);
lean_dec_ref(v_newDomain_1406_);
lean_dec_ref(v_inst_1404_);
lean_dec_ref(v_inst_1403_);
v___x_1422_ = lean_apply_2(v_toPure_1409_, lean_box(0), v_e_1405_);
return v___x_1422_;
}
}
}
else
{
lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; 
lean_dec_ref(v_newBody_1407_);
lean_dec_ref(v_newDomain_1406_);
lean_dec_ref(v_e_1405_);
lean_dec_ref(v_inst_1403_);
v___x_1423_ = l_Lean_instInhabitedExpr;
v___x_1424_ = l_instInhabitedOfMonad___redArg(v_inst_1404_, v___x_1423_);
v___x_1425_ = lean_obj_once(&l_Lean_Expr_updateLambdaS_x21___redArg___closed__2, &l_Lean_Expr_updateLambdaS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateLambdaS_x21___redArg___closed__2);
v___x_1426_ = l_panic___redArg(v___x_1424_, v___x_1425_);
lean_dec(v___x_1424_);
return v___x_1426_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLambdaS_x21(lean_object* v_m_1427_, lean_object* v_inst_1428_, lean_object* v_inst_1429_, lean_object* v_e_1430_, lean_object* v_newDomain_1431_, lean_object* v_newBody_1432_){
_start:
{
if (lean_obj_tag(v_e_1430_) == 6)
{
lean_object* v_toApplicative_1433_; lean_object* v_toPure_1434_; lean_object* v_binderName_1435_; lean_object* v_binderType_1436_; lean_object* v_body_1437_; uint8_t v_binderInfo_1438_; size_t v___x_1439_; size_t v___x_1440_; uint8_t v___x_1441_; 
v_toApplicative_1433_ = lean_ctor_get(v_inst_1429_, 0);
v_toPure_1434_ = lean_ctor_get(v_toApplicative_1433_, 1);
v_binderName_1435_ = lean_ctor_get(v_e_1430_, 0);
v_binderType_1436_ = lean_ctor_get(v_e_1430_, 1);
v_body_1437_ = lean_ctor_get(v_e_1430_, 2);
v_binderInfo_1438_ = lean_ctor_get_uint8(v_e_1430_, sizeof(void*)*3 + 8);
v___x_1439_ = lean_ptr_addr(v_binderType_1436_);
v___x_1440_ = lean_ptr_addr(v_newDomain_1431_);
v___x_1441_ = lean_usize_dec_eq(v___x_1439_, v___x_1440_);
if (v___x_1441_ == 0)
{
lean_object* v___x_1442_; 
lean_inc(v_binderName_1435_);
lean_dec_ref_known(v_e_1430_, 3);
v___x_1442_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v_inst_1428_, v_inst_1429_, v_binderName_1435_, v_binderInfo_1438_, v_newDomain_1431_, v_newBody_1432_);
return v___x_1442_;
}
else
{
size_t v___x_1443_; size_t v___x_1444_; uint8_t v___x_1445_; 
v___x_1443_ = lean_ptr_addr(v_body_1437_);
v___x_1444_ = lean_ptr_addr(v_newBody_1432_);
v___x_1445_ = lean_usize_dec_eq(v___x_1443_, v___x_1444_);
if (v___x_1445_ == 0)
{
lean_object* v___x_1446_; 
lean_inc(v_binderName_1435_);
lean_dec_ref_known(v_e_1430_, 3);
v___x_1446_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v_inst_1428_, v_inst_1429_, v_binderName_1435_, v_binderInfo_1438_, v_newDomain_1431_, v_newBody_1432_);
return v___x_1446_;
}
else
{
lean_object* v___x_1447_; 
lean_inc(v_toPure_1434_);
lean_dec_ref(v_newBody_1432_);
lean_dec_ref(v_newDomain_1431_);
lean_dec_ref(v_inst_1429_);
lean_dec_ref(v_inst_1428_);
v___x_1447_ = lean_apply_2(v_toPure_1434_, lean_box(0), v_e_1430_);
return v___x_1447_;
}
}
}
else
{
lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; 
lean_dec_ref(v_newBody_1432_);
lean_dec_ref(v_newDomain_1431_);
lean_dec_ref(v_e_1430_);
lean_dec_ref(v_inst_1428_);
v___x_1448_ = l_Lean_instInhabitedExpr;
v___x_1449_ = l_instInhabitedOfMonad___redArg(v_inst_1429_, v___x_1448_);
v___x_1450_ = lean_obj_once(&l_Lean_Expr_updateLambdaS_x21___redArg___closed__2, &l_Lean_Expr_updateLambdaS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateLambdaS_x21___redArg___closed__2);
v___x_1451_ = l_panic___redArg(v___x_1449_, v___x_1450_);
lean_dec(v___x_1449_);
return v___x_1451_;
}
}
}
static lean_object* _init_l_Lean_Expr_updateLetS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; 
v___x_1454_ = ((lean_object*)(l_Lean_Expr_updateLetS_x21___redArg___closed__1));
v___x_1455_ = lean_unsigned_to_nat(34u);
v___x_1456_ = lean_unsigned_to_nat(174u);
v___x_1457_ = ((lean_object*)(l_Lean_Expr_updateLetS_x21___redArg___closed__0));
v___x_1458_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1459_ = l_mkPanicMessageWithDecl(v___x_1458_, v___x_1457_, v___x_1456_, v___x_1455_, v___x_1454_);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLetS_x21___redArg(lean_object* v_inst_1460_, lean_object* v_inst_1461_, lean_object* v_e_1462_, lean_object* v_newType_1463_, lean_object* v_newVal_1464_, lean_object* v_newBody_1465_){
_start:
{
if (lean_obj_tag(v_e_1462_) == 8)
{
lean_object* v_toApplicative_1466_; lean_object* v_toPure_1467_; lean_object* v_declName_1468_; lean_object* v_type_1469_; lean_object* v_value_1470_; lean_object* v_body_1471_; uint8_t v_nondep_1472_; size_t v___x_1473_; size_t v___x_1474_; uint8_t v___x_1475_; 
v_toApplicative_1466_ = lean_ctor_get(v_inst_1461_, 0);
v_toPure_1467_ = lean_ctor_get(v_toApplicative_1466_, 1);
v_declName_1468_ = lean_ctor_get(v_e_1462_, 0);
v_type_1469_ = lean_ctor_get(v_e_1462_, 1);
v_value_1470_ = lean_ctor_get(v_e_1462_, 2);
v_body_1471_ = lean_ctor_get(v_e_1462_, 3);
v_nondep_1472_ = lean_ctor_get_uint8(v_e_1462_, sizeof(void*)*4 + 8);
v___x_1473_ = lean_ptr_addr(v_type_1469_);
v___x_1474_ = lean_ptr_addr(v_newType_1463_);
v___x_1475_ = lean_usize_dec_eq(v___x_1473_, v___x_1474_);
if (v___x_1475_ == 0)
{
lean_object* v___x_1476_; 
lean_inc(v_declName_1468_);
lean_dec_ref_known(v_e_1462_, 4);
v___x_1476_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1460_, v_inst_1461_, v_declName_1468_, v_newType_1463_, v_newVal_1464_, v_newBody_1465_, v_nondep_1472_);
return v___x_1476_;
}
else
{
size_t v___x_1477_; size_t v___x_1478_; uint8_t v___x_1479_; 
v___x_1477_ = lean_ptr_addr(v_value_1470_);
v___x_1478_ = lean_ptr_addr(v_newVal_1464_);
v___x_1479_ = lean_usize_dec_eq(v___x_1477_, v___x_1478_);
if (v___x_1479_ == 0)
{
lean_object* v___x_1480_; 
lean_inc(v_declName_1468_);
lean_dec_ref_known(v_e_1462_, 4);
v___x_1480_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1460_, v_inst_1461_, v_declName_1468_, v_newType_1463_, v_newVal_1464_, v_newBody_1465_, v_nondep_1472_);
return v___x_1480_;
}
else
{
size_t v___x_1481_; size_t v___x_1482_; uint8_t v___x_1483_; 
v___x_1481_ = lean_ptr_addr(v_body_1471_);
v___x_1482_ = lean_ptr_addr(v_newBody_1465_);
v___x_1483_ = lean_usize_dec_eq(v___x_1481_, v___x_1482_);
if (v___x_1483_ == 0)
{
lean_object* v___x_1484_; 
lean_inc(v_declName_1468_);
lean_dec_ref_known(v_e_1462_, 4);
v___x_1484_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1460_, v_inst_1461_, v_declName_1468_, v_newType_1463_, v_newVal_1464_, v_newBody_1465_, v_nondep_1472_);
return v___x_1484_;
}
else
{
lean_object* v___x_1485_; 
lean_inc(v_toPure_1467_);
lean_dec_ref(v_newBody_1465_);
lean_dec_ref(v_newVal_1464_);
lean_dec_ref(v_newType_1463_);
lean_dec_ref(v_inst_1461_);
lean_dec_ref(v_inst_1460_);
v___x_1485_ = lean_apply_2(v_toPure_1467_, lean_box(0), v_e_1462_);
return v___x_1485_;
}
}
}
}
else
{
lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; 
lean_dec_ref(v_newBody_1465_);
lean_dec_ref(v_newVal_1464_);
lean_dec_ref(v_newType_1463_);
lean_dec_ref(v_e_1462_);
lean_dec_ref(v_inst_1460_);
v___x_1486_ = l_Lean_instInhabitedExpr;
v___x_1487_ = l_instInhabitedOfMonad___redArg(v_inst_1461_, v___x_1486_);
v___x_1488_ = lean_obj_once(&l_Lean_Expr_updateLetS_x21___redArg___closed__2, &l_Lean_Expr_updateLetS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateLetS_x21___redArg___closed__2);
v___x_1489_ = l_panic___redArg(v___x_1487_, v___x_1488_);
lean_dec(v___x_1487_);
return v___x_1489_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLetS_x21(lean_object* v_m_1490_, lean_object* v_inst_1491_, lean_object* v_inst_1492_, lean_object* v_e_1493_, lean_object* v_newType_1494_, lean_object* v_newVal_1495_, lean_object* v_newBody_1496_){
_start:
{
if (lean_obj_tag(v_e_1493_) == 8)
{
lean_object* v_toApplicative_1497_; lean_object* v_toPure_1498_; lean_object* v_declName_1499_; lean_object* v_type_1500_; lean_object* v_value_1501_; lean_object* v_body_1502_; uint8_t v_nondep_1503_; size_t v___x_1504_; size_t v___x_1505_; uint8_t v___x_1506_; 
v_toApplicative_1497_ = lean_ctor_get(v_inst_1492_, 0);
v_toPure_1498_ = lean_ctor_get(v_toApplicative_1497_, 1);
v_declName_1499_ = lean_ctor_get(v_e_1493_, 0);
v_type_1500_ = lean_ctor_get(v_e_1493_, 1);
v_value_1501_ = lean_ctor_get(v_e_1493_, 2);
v_body_1502_ = lean_ctor_get(v_e_1493_, 3);
v_nondep_1503_ = lean_ctor_get_uint8(v_e_1493_, sizeof(void*)*4 + 8);
v___x_1504_ = lean_ptr_addr(v_type_1500_);
v___x_1505_ = lean_ptr_addr(v_newType_1494_);
v___x_1506_ = lean_usize_dec_eq(v___x_1504_, v___x_1505_);
if (v___x_1506_ == 0)
{
lean_object* v___x_1507_; 
lean_inc(v_declName_1499_);
lean_dec_ref_known(v_e_1493_, 4);
v___x_1507_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1491_, v_inst_1492_, v_declName_1499_, v_newType_1494_, v_newVal_1495_, v_newBody_1496_, v_nondep_1503_);
return v___x_1507_;
}
else
{
size_t v___x_1508_; size_t v___x_1509_; uint8_t v___x_1510_; 
v___x_1508_ = lean_ptr_addr(v_value_1501_);
v___x_1509_ = lean_ptr_addr(v_newVal_1495_);
v___x_1510_ = lean_usize_dec_eq(v___x_1508_, v___x_1509_);
if (v___x_1510_ == 0)
{
lean_object* v___x_1511_; 
lean_inc(v_declName_1499_);
lean_dec_ref_known(v_e_1493_, 4);
v___x_1511_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1491_, v_inst_1492_, v_declName_1499_, v_newType_1494_, v_newVal_1495_, v_newBody_1496_, v_nondep_1503_);
return v___x_1511_;
}
else
{
size_t v___x_1512_; size_t v___x_1513_; uint8_t v___x_1514_; 
v___x_1512_ = lean_ptr_addr(v_body_1502_);
v___x_1513_ = lean_ptr_addr(v_newBody_1496_);
v___x_1514_ = lean_usize_dec_eq(v___x_1512_, v___x_1513_);
if (v___x_1514_ == 0)
{
lean_object* v___x_1515_; 
lean_inc(v_declName_1499_);
lean_dec_ref_known(v_e_1493_, 4);
v___x_1515_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1491_, v_inst_1492_, v_declName_1499_, v_newType_1494_, v_newVal_1495_, v_newBody_1496_, v_nondep_1503_);
return v___x_1515_;
}
else
{
lean_object* v___x_1516_; 
lean_inc(v_toPure_1498_);
lean_dec_ref(v_newBody_1496_);
lean_dec_ref(v_newVal_1495_);
lean_dec_ref(v_newType_1494_);
lean_dec_ref(v_inst_1492_);
lean_dec_ref(v_inst_1491_);
v___x_1516_ = lean_apply_2(v_toPure_1498_, lean_box(0), v_e_1493_);
return v___x_1516_;
}
}
}
}
else
{
lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; 
lean_dec_ref(v_newBody_1496_);
lean_dec_ref(v_newVal_1495_);
lean_dec_ref(v_newType_1494_);
lean_dec_ref(v_e_1493_);
lean_dec_ref(v_inst_1491_);
v___x_1517_ = l_Lean_instInhabitedExpr;
v___x_1518_ = l_instInhabitedOfMonad___redArg(v_inst_1492_, v___x_1517_);
v___x_1519_ = lean_obj_once(&l_Lean_Expr_updateLetS_x21___redArg___closed__2, &l_Lean_Expr_updateLetS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateLetS_x21___redArg___closed__2);
v___x_1520_ = l_panic___redArg(v___x_1518_, v___x_1519_);
lean_dec(v___x_1518_);
return v___x_1520_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___redArg___lam__0(lean_object* v_inst_1521_, lean_object* v_inst_1522_, lean_object* v_a_u2082_1523_, lean_object* v_____do__lift_1524_){
_start:
{
lean_object* v___x_1525_; 
v___x_1525_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1521_, v_inst_1522_, v_____do__lift_1524_, v_a_u2082_1523_);
return v___x_1525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___redArg(lean_object* v_inst_1526_, lean_object* v_inst_1527_, lean_object* v_f_1528_, lean_object* v_a_u2081_1529_, lean_object* v_a_u2082_1530_){
_start:
{
lean_object* v_toBind_1531_; lean_object* v___f_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; 
v_toBind_1531_ = lean_ctor_get(v_inst_1527_, 1);
lean_inc(v_toBind_1531_);
lean_inc_ref(v_inst_1527_);
lean_inc_ref(v_inst_1526_);
v___f_1532_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2082___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1532_, 0, v_inst_1526_);
lean_closure_set(v___f_1532_, 1, v_inst_1527_);
lean_closure_set(v___f_1532_, 2, v_a_u2082_1530_);
v___x_1533_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1526_, v_inst_1527_, v_f_1528_, v_a_u2081_1529_);
v___x_1534_ = lean_apply_4(v_toBind_1531_, lean_box(0), lean_box(0), v___x_1533_, v___f_1532_);
return v___x_1534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082(lean_object* v_m_1535_, lean_object* v_inst_1536_, lean_object* v_inst_1537_, lean_object* v_f_1538_, lean_object* v_a_u2081_1539_, lean_object* v_a_u2082_1540_){
_start:
{
lean_object* v___x_1541_; 
v___x_1541_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___redArg(v_inst_1536_, v_inst_1537_, v_f_1538_, v_a_u2081_1539_, v_a_u2082_1540_);
return v___x_1541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___redArg___lam__0(lean_object* v_inst_1542_, lean_object* v_inst_1543_, lean_object* v_a_u2083_1544_, lean_object* v_____do__lift_1545_){
_start:
{
lean_object* v___x_1546_; 
v___x_1546_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1542_, v_inst_1543_, v_____do__lift_1545_, v_a_u2083_1544_);
return v___x_1546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___redArg(lean_object* v_inst_1547_, lean_object* v_inst_1548_, lean_object* v_f_1549_, lean_object* v_a_u2081_1550_, lean_object* v_a_u2082_1551_, lean_object* v_a_u2083_1552_){
_start:
{
lean_object* v_toBind_1553_; lean_object* v___f_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; 
v_toBind_1553_ = lean_ctor_get(v_inst_1548_, 1);
lean_inc(v_toBind_1553_);
lean_inc_ref(v_inst_1548_);
lean_inc_ref(v_inst_1547_);
v___f_1554_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2083___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1554_, 0, v_inst_1547_);
lean_closure_set(v___f_1554_, 1, v_inst_1548_);
lean_closure_set(v___f_1554_, 2, v_a_u2083_1552_);
v___x_1555_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___redArg(v_inst_1547_, v_inst_1548_, v_f_1549_, v_a_u2081_1550_, v_a_u2082_1551_);
v___x_1556_ = lean_apply_4(v_toBind_1553_, lean_box(0), lean_box(0), v___x_1555_, v___f_1554_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083(lean_object* v_m_1557_, lean_object* v_inst_1558_, lean_object* v_inst_1559_, lean_object* v_f_1560_, lean_object* v_a_u2081_1561_, lean_object* v_a_u2082_1562_, lean_object* v_a_u2083_1563_){
_start:
{
lean_object* v___x_1564_; 
v___x_1564_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___redArg(v_inst_1558_, v_inst_1559_, v_f_1560_, v_a_u2081_1561_, v_a_u2082_1562_, v_a_u2083_1563_);
return v___x_1564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___redArg___lam__0(lean_object* v_inst_1565_, lean_object* v_inst_1566_, lean_object* v_a_u2084_1567_, lean_object* v_____do__lift_1568_){
_start:
{
lean_object* v___x_1569_; 
v___x_1569_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1565_, v_inst_1566_, v_____do__lift_1568_, v_a_u2084_1567_);
return v___x_1569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___redArg(lean_object* v_inst_1570_, lean_object* v_inst_1571_, lean_object* v_f_1572_, lean_object* v_a_u2081_1573_, lean_object* v_a_u2082_1574_, lean_object* v_a_u2083_1575_, lean_object* v_a_u2084_1576_){
_start:
{
lean_object* v_toBind_1577_; lean_object* v___f_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; 
v_toBind_1577_ = lean_ctor_get(v_inst_1571_, 1);
lean_inc(v_toBind_1577_);
lean_inc_ref(v_inst_1571_);
lean_inc_ref(v_inst_1570_);
v___f_1578_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2084___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1578_, 0, v_inst_1570_);
lean_closure_set(v___f_1578_, 1, v_inst_1571_);
lean_closure_set(v___f_1578_, 2, v_a_u2084_1576_);
v___x_1579_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___redArg(v_inst_1570_, v_inst_1571_, v_f_1572_, v_a_u2081_1573_, v_a_u2082_1574_, v_a_u2083_1575_);
v___x_1580_ = lean_apply_4(v_toBind_1577_, lean_box(0), lean_box(0), v___x_1579_, v___f_1578_);
return v___x_1580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084(lean_object* v_m_1581_, lean_object* v_inst_1582_, lean_object* v_inst_1583_, lean_object* v_f_1584_, lean_object* v_a_u2081_1585_, lean_object* v_a_u2082_1586_, lean_object* v_a_u2083_1587_, lean_object* v_a_u2084_1588_){
_start:
{
lean_object* v___x_1589_; 
v___x_1589_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___redArg(v_inst_1582_, v_inst_1583_, v_f_1584_, v_a_u2081_1585_, v_a_u2082_1586_, v_a_u2083_1587_, v_a_u2084_1588_);
return v___x_1589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2085___redArg___lam__0(lean_object* v_inst_1590_, lean_object* v_inst_1591_, lean_object* v_a_u2085_1592_, lean_object* v_____do__lift_1593_){
_start:
{
lean_object* v___x_1594_; 
v___x_1594_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1590_, v_inst_1591_, v_____do__lift_1593_, v_a_u2085_1592_);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2085___redArg(lean_object* v_inst_1595_, lean_object* v_inst_1596_, lean_object* v_f_1597_, lean_object* v_a_u2081_1598_, lean_object* v_a_u2082_1599_, lean_object* v_a_u2083_1600_, lean_object* v_a_u2084_1601_, lean_object* v_a_u2085_1602_){
_start:
{
lean_object* v_toBind_1603_; lean_object* v___f_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; 
v_toBind_1603_ = lean_ctor_get(v_inst_1596_, 1);
lean_inc(v_toBind_1603_);
lean_inc_ref(v_inst_1596_);
lean_inc_ref(v_inst_1595_);
v___f_1604_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2085___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1604_, 0, v_inst_1595_);
lean_closure_set(v___f_1604_, 1, v_inst_1596_);
lean_closure_set(v___f_1604_, 2, v_a_u2085_1602_);
v___x_1605_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___redArg(v_inst_1595_, v_inst_1596_, v_f_1597_, v_a_u2081_1598_, v_a_u2082_1599_, v_a_u2083_1600_, v_a_u2084_1601_);
v___x_1606_ = lean_apply_4(v_toBind_1603_, lean_box(0), lean_box(0), v___x_1605_, v___f_1604_);
return v___x_1606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2085(lean_object* v_m_1607_, lean_object* v_inst_1608_, lean_object* v_inst_1609_, lean_object* v_f_1610_, lean_object* v_a_u2081_1611_, lean_object* v_a_u2082_1612_, lean_object* v_a_u2083_1613_, lean_object* v_a_u2084_1614_, lean_object* v_a_u2085_1615_){
_start:
{
lean_object* v___x_1616_; 
v___x_1616_ = l_Lean_Meta_Sym_Internal_mkAppS_u2085___redArg(v_inst_1608_, v_inst_1609_, v_f_1610_, v_a_u2081_1611_, v_a_u2082_1612_, v_a_u2083_1613_, v_a_u2084_1614_, v_a_u2085_1615_);
return v___x_1616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2086___redArg___lam__0(lean_object* v_inst_1617_, lean_object* v_inst_1618_, lean_object* v_a_u2086_1619_, lean_object* v_____do__lift_1620_){
_start:
{
lean_object* v___x_1621_; 
v___x_1621_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1617_, v_inst_1618_, v_____do__lift_1620_, v_a_u2086_1619_);
return v___x_1621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2086___redArg(lean_object* v_inst_1622_, lean_object* v_inst_1623_, lean_object* v_f_1624_, lean_object* v_a_u2081_1625_, lean_object* v_a_u2082_1626_, lean_object* v_a_u2083_1627_, lean_object* v_a_u2084_1628_, lean_object* v_a_u2085_1629_, lean_object* v_a_u2086_1630_){
_start:
{
lean_object* v_toBind_1631_; lean_object* v___f_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; 
v_toBind_1631_ = lean_ctor_get(v_inst_1623_, 1);
lean_inc(v_toBind_1631_);
lean_inc_ref(v_inst_1623_);
lean_inc_ref(v_inst_1622_);
v___f_1632_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2086___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1632_, 0, v_inst_1622_);
lean_closure_set(v___f_1632_, 1, v_inst_1623_);
lean_closure_set(v___f_1632_, 2, v_a_u2086_1630_);
v___x_1633_ = l_Lean_Meta_Sym_Internal_mkAppS_u2085___redArg(v_inst_1622_, v_inst_1623_, v_f_1624_, v_a_u2081_1625_, v_a_u2082_1626_, v_a_u2083_1627_, v_a_u2084_1628_, v_a_u2085_1629_);
v___x_1634_ = lean_apply_4(v_toBind_1631_, lean_box(0), lean_box(0), v___x_1633_, v___f_1632_);
return v___x_1634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2086(lean_object* v_m_1635_, lean_object* v_inst_1636_, lean_object* v_inst_1637_, lean_object* v_f_1638_, lean_object* v_a_u2081_1639_, lean_object* v_a_u2082_1640_, lean_object* v_a_u2083_1641_, lean_object* v_a_u2084_1642_, lean_object* v_a_u2085_1643_, lean_object* v_a_u2086_1644_){
_start:
{
lean_object* v___x_1645_; 
v___x_1645_ = l_Lean_Meta_Sym_Internal_mkAppS_u2086___redArg(v_inst_1636_, v_inst_1637_, v_f_1638_, v_a_u2081_1639_, v_a_u2082_1640_, v_a_u2083_1641_, v_a_u2084_1642_, v_a_u2085_1643_, v_a_u2086_1644_);
return v___x_1645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2087___redArg___lam__0(lean_object* v_inst_1646_, lean_object* v_inst_1647_, lean_object* v_a_u2087_1648_, lean_object* v_____do__lift_1649_){
_start:
{
lean_object* v___x_1650_; 
v___x_1650_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1646_, v_inst_1647_, v_____do__lift_1649_, v_a_u2087_1648_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2087___redArg(lean_object* v_inst_1651_, lean_object* v_inst_1652_, lean_object* v_f_1653_, lean_object* v_a_u2081_1654_, lean_object* v_a_u2082_1655_, lean_object* v_a_u2083_1656_, lean_object* v_a_u2084_1657_, lean_object* v_a_u2085_1658_, lean_object* v_a_u2086_1659_, lean_object* v_a_u2087_1660_){
_start:
{
lean_object* v_toBind_1661_; lean_object* v___f_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; 
v_toBind_1661_ = lean_ctor_get(v_inst_1652_, 1);
lean_inc(v_toBind_1661_);
lean_inc_ref(v_inst_1652_);
lean_inc_ref(v_inst_1651_);
v___f_1662_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2087___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1662_, 0, v_inst_1651_);
lean_closure_set(v___f_1662_, 1, v_inst_1652_);
lean_closure_set(v___f_1662_, 2, v_a_u2087_1660_);
v___x_1663_ = l_Lean_Meta_Sym_Internal_mkAppS_u2086___redArg(v_inst_1651_, v_inst_1652_, v_f_1653_, v_a_u2081_1654_, v_a_u2082_1655_, v_a_u2083_1656_, v_a_u2084_1657_, v_a_u2085_1658_, v_a_u2086_1659_);
v___x_1664_ = lean_apply_4(v_toBind_1661_, lean_box(0), lean_box(0), v___x_1663_, v___f_1662_);
return v___x_1664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2087(lean_object* v_m_1665_, lean_object* v_inst_1666_, lean_object* v_inst_1667_, lean_object* v_f_1668_, lean_object* v_a_u2081_1669_, lean_object* v_a_u2082_1670_, lean_object* v_a_u2083_1671_, lean_object* v_a_u2084_1672_, lean_object* v_a_u2085_1673_, lean_object* v_a_u2086_1674_, lean_object* v_a_u2087_1675_){
_start:
{
lean_object* v___x_1676_; 
v___x_1676_ = l_Lean_Meta_Sym_Internal_mkAppS_u2087___redArg(v_inst_1666_, v_inst_1667_, v_f_1668_, v_a_u2081_1669_, v_a_u2082_1670_, v_a_u2083_1671_, v_a_u2084_1672_, v_a_u2085_1673_, v_a_u2086_1674_, v_a_u2087_1675_);
return v___x_1676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2088___redArg___lam__0(lean_object* v_inst_1677_, lean_object* v_inst_1678_, lean_object* v_a_u2088_1679_, lean_object* v_____do__lift_1680_){
_start:
{
lean_object* v___x_1681_; 
v___x_1681_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1677_, v_inst_1678_, v_____do__lift_1680_, v_a_u2088_1679_);
return v___x_1681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2088___redArg(lean_object* v_inst_1682_, lean_object* v_inst_1683_, lean_object* v_f_1684_, lean_object* v_a_u2081_1685_, lean_object* v_a_u2082_1686_, lean_object* v_a_u2083_1687_, lean_object* v_a_u2084_1688_, lean_object* v_a_u2085_1689_, lean_object* v_a_u2086_1690_, lean_object* v_a_u2087_1691_, lean_object* v_a_u2088_1692_){
_start:
{
lean_object* v_toBind_1693_; lean_object* v___f_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; 
v_toBind_1693_ = lean_ctor_get(v_inst_1683_, 1);
lean_inc(v_toBind_1693_);
lean_inc_ref(v_inst_1683_);
lean_inc_ref(v_inst_1682_);
v___f_1694_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2088___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1694_, 0, v_inst_1682_);
lean_closure_set(v___f_1694_, 1, v_inst_1683_);
lean_closure_set(v___f_1694_, 2, v_a_u2088_1692_);
v___x_1695_ = l_Lean_Meta_Sym_Internal_mkAppS_u2087___redArg(v_inst_1682_, v_inst_1683_, v_f_1684_, v_a_u2081_1685_, v_a_u2082_1686_, v_a_u2083_1687_, v_a_u2084_1688_, v_a_u2085_1689_, v_a_u2086_1690_, v_a_u2087_1691_);
v___x_1696_ = lean_apply_4(v_toBind_1693_, lean_box(0), lean_box(0), v___x_1695_, v___f_1694_);
return v___x_1696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2088(lean_object* v_m_1697_, lean_object* v_inst_1698_, lean_object* v_inst_1699_, lean_object* v_f_1700_, lean_object* v_a_u2081_1701_, lean_object* v_a_u2082_1702_, lean_object* v_a_u2083_1703_, lean_object* v_a_u2084_1704_, lean_object* v_a_u2085_1705_, lean_object* v_a_u2086_1706_, lean_object* v_a_u2087_1707_, lean_object* v_a_u2088_1708_){
_start:
{
lean_object* v___x_1709_; 
v___x_1709_ = l_Lean_Meta_Sym_Internal_mkAppS_u2088___redArg(v_inst_1698_, v_inst_1699_, v_f_1700_, v_a_u2081_1701_, v_a_u2082_1702_, v_a_u2083_1703_, v_a_u2084_1704_, v_a_u2085_1705_, v_a_u2086_1706_, v_a_u2087_1707_, v_a_u2088_1708_);
return v___x_1709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2089___redArg___lam__0(lean_object* v_inst_1710_, lean_object* v_inst_1711_, lean_object* v_a_u2089_1712_, lean_object* v_____do__lift_1713_){
_start:
{
lean_object* v___x_1714_; 
v___x_1714_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1710_, v_inst_1711_, v_____do__lift_1713_, v_a_u2089_1712_);
return v___x_1714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2089___redArg(lean_object* v_inst_1715_, lean_object* v_inst_1716_, lean_object* v_f_1717_, lean_object* v_a_u2081_1718_, lean_object* v_a_u2082_1719_, lean_object* v_a_u2083_1720_, lean_object* v_a_u2084_1721_, lean_object* v_a_u2085_1722_, lean_object* v_a_u2086_1723_, lean_object* v_a_u2087_1724_, lean_object* v_a_u2088_1725_, lean_object* v_a_u2089_1726_){
_start:
{
lean_object* v_toBind_1727_; lean_object* v___f_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; 
v_toBind_1727_ = lean_ctor_get(v_inst_1716_, 1);
lean_inc(v_toBind_1727_);
lean_inc_ref(v_inst_1716_);
lean_inc_ref(v_inst_1715_);
v___f_1728_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2089___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1728_, 0, v_inst_1715_);
lean_closure_set(v___f_1728_, 1, v_inst_1716_);
lean_closure_set(v___f_1728_, 2, v_a_u2089_1726_);
v___x_1729_ = l_Lean_Meta_Sym_Internal_mkAppS_u2088___redArg(v_inst_1715_, v_inst_1716_, v_f_1717_, v_a_u2081_1718_, v_a_u2082_1719_, v_a_u2083_1720_, v_a_u2084_1721_, v_a_u2085_1722_, v_a_u2086_1723_, v_a_u2087_1724_, v_a_u2088_1725_);
v___x_1730_ = lean_apply_4(v_toBind_1727_, lean_box(0), lean_box(0), v___x_1729_, v___f_1728_);
return v___x_1730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2089(lean_object* v_m_1731_, lean_object* v_inst_1732_, lean_object* v_inst_1733_, lean_object* v_f_1734_, lean_object* v_a_u2081_1735_, lean_object* v_a_u2082_1736_, lean_object* v_a_u2083_1737_, lean_object* v_a_u2084_1738_, lean_object* v_a_u2085_1739_, lean_object* v_a_u2086_1740_, lean_object* v_a_u2087_1741_, lean_object* v_a_u2088_1742_, lean_object* v_a_u2089_1743_){
_start:
{
lean_object* v___x_1744_; 
v___x_1744_ = l_Lean_Meta_Sym_Internal_mkAppS_u2089___redArg(v_inst_1732_, v_inst_1733_, v_f_1734_, v_a_u2081_1735_, v_a_u2082_1736_, v_a_u2083_1737_, v_a_u2084_1738_, v_a_u2085_1739_, v_a_u2086_1740_, v_a_u2087_1741_, v_a_u2088_1742_, v_a_u2089_1743_);
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2080___redArg___lam__0(lean_object* v_inst_1745_, lean_object* v_inst_1746_, lean_object* v_a_u2081_u2080_1747_, lean_object* v_____do__lift_1748_){
_start:
{
lean_object* v___x_1749_; 
v___x_1749_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1745_, v_inst_1746_, v_____do__lift_1748_, v_a_u2081_u2080_1747_);
return v___x_1749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2080___redArg(lean_object* v_inst_1750_, lean_object* v_inst_1751_, lean_object* v_f_1752_, lean_object* v_a_u2081_1753_, lean_object* v_a_u2082_1754_, lean_object* v_a_u2083_1755_, lean_object* v_a_u2084_1756_, lean_object* v_a_u2085_1757_, lean_object* v_a_u2086_1758_, lean_object* v_a_u2087_1759_, lean_object* v_a_u2088_1760_, lean_object* v_a_u2089_1761_, lean_object* v_a_u2081_u2080_1762_){
_start:
{
lean_object* v_toBind_1763_; lean_object* v___f_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; 
v_toBind_1763_ = lean_ctor_get(v_inst_1751_, 1);
lean_inc(v_toBind_1763_);
lean_inc_ref(v_inst_1751_);
lean_inc_ref(v_inst_1750_);
v___f_1764_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2080___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1764_, 0, v_inst_1750_);
lean_closure_set(v___f_1764_, 1, v_inst_1751_);
lean_closure_set(v___f_1764_, 2, v_a_u2081_u2080_1762_);
v___x_1765_ = l_Lean_Meta_Sym_Internal_mkAppS_u2089___redArg(v_inst_1750_, v_inst_1751_, v_f_1752_, v_a_u2081_1753_, v_a_u2082_1754_, v_a_u2083_1755_, v_a_u2084_1756_, v_a_u2085_1757_, v_a_u2086_1758_, v_a_u2087_1759_, v_a_u2088_1760_, v_a_u2089_1761_);
v___x_1766_ = lean_apply_4(v_toBind_1763_, lean_box(0), lean_box(0), v___x_1765_, v___f_1764_);
return v___x_1766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2080(lean_object* v_m_1767_, lean_object* v_inst_1768_, lean_object* v_inst_1769_, lean_object* v_f_1770_, lean_object* v_a_u2081_1771_, lean_object* v_a_u2082_1772_, lean_object* v_a_u2083_1773_, lean_object* v_a_u2084_1774_, lean_object* v_a_u2085_1775_, lean_object* v_a_u2086_1776_, lean_object* v_a_u2087_1777_, lean_object* v_a_u2088_1778_, lean_object* v_a_u2089_1779_, lean_object* v_a_u2081_u2080_1780_){
_start:
{
lean_object* v___x_1781_; 
v___x_1781_ = l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2080___redArg(v_inst_1768_, v_inst_1769_, v_f_1770_, v_a_u2081_1771_, v_a_u2082_1772_, v_a_u2083_1773_, v_a_u2084_1774_, v_a_u2085_1775_, v_a_u2086_1776_, v_a_u2087_1777_, v_a_u2088_1778_, v_a_u2089_1779_, v_a_u2081_u2080_1780_);
return v___x_1781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2081___redArg___lam__0(lean_object* v_inst_1782_, lean_object* v_inst_1783_, lean_object* v_a_u2081_u2081_1784_, lean_object* v_____do__lift_1785_){
_start:
{
lean_object* v___x_1786_; 
v___x_1786_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1782_, v_inst_1783_, v_____do__lift_1785_, v_a_u2081_u2081_1784_);
return v___x_1786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2081___redArg(lean_object* v_inst_1787_, lean_object* v_inst_1788_, lean_object* v_f_1789_, lean_object* v_a_u2081_1790_, lean_object* v_a_u2082_1791_, lean_object* v_a_u2083_1792_, lean_object* v_a_u2084_1793_, lean_object* v_a_u2085_1794_, lean_object* v_a_u2086_1795_, lean_object* v_a_u2087_1796_, lean_object* v_a_u2088_1797_, lean_object* v_a_u2089_1798_, lean_object* v_a_u2081_u2080_1799_, lean_object* v_a_u2081_u2081_1800_){
_start:
{
lean_object* v_toBind_1801_; lean_object* v___f_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; 
v_toBind_1801_ = lean_ctor_get(v_inst_1788_, 1);
lean_inc(v_toBind_1801_);
lean_inc_ref(v_inst_1788_);
lean_inc_ref(v_inst_1787_);
v___f_1802_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2081___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1802_, 0, v_inst_1787_);
lean_closure_set(v___f_1802_, 1, v_inst_1788_);
lean_closure_set(v___f_1802_, 2, v_a_u2081_u2081_1800_);
v___x_1803_ = l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2080___redArg(v_inst_1787_, v_inst_1788_, v_f_1789_, v_a_u2081_1790_, v_a_u2082_1791_, v_a_u2083_1792_, v_a_u2084_1793_, v_a_u2085_1794_, v_a_u2086_1795_, v_a_u2087_1796_, v_a_u2088_1797_, v_a_u2089_1798_, v_a_u2081_u2080_1799_);
v___x_1804_ = lean_apply_4(v_toBind_1801_, lean_box(0), lean_box(0), v___x_1803_, v___f_1802_);
return v___x_1804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2081(lean_object* v_m_1805_, lean_object* v_inst_1806_, lean_object* v_inst_1807_, lean_object* v_f_1808_, lean_object* v_a_u2081_1809_, lean_object* v_a_u2082_1810_, lean_object* v_a_u2083_1811_, lean_object* v_a_u2084_1812_, lean_object* v_a_u2085_1813_, lean_object* v_a_u2086_1814_, lean_object* v_a_u2087_1815_, lean_object* v_a_u2088_1816_, lean_object* v_a_u2089_1817_, lean_object* v_a_u2081_u2080_1818_, lean_object* v_a_u2081_u2081_1819_){
_start:
{
lean_object* v___x_1820_; 
v___x_1820_ = l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2081___redArg(v_inst_1806_, v_inst_1807_, v_f_1808_, v_a_u2081_1809_, v_a_u2082_1810_, v_a_u2083_1811_, v_a_u2084_1812_, v_a_u2085_1813_, v_a_u2086_1814_, v_a_u2087_1815_, v_a_u2088_1816_, v_a_u2089_1817_, v_a_u2081_u2080_1818_, v_a_u2081_u2081_1819_);
return v___x_1820_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg___lam__0___boxed(lean_object* v_i_1821_, lean_object* v_inst_1822_, lean_object* v_inst_1823_, lean_object* v_args_1824_, lean_object* v_endIdx_1825_, lean_object* v_____do__lift_1826_){
_start:
{
lean_object* v_res_1827_; 
v_res_1827_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg___lam__0(v_i_1821_, v_inst_1822_, v_inst_1823_, v_args_1824_, v_endIdx_1825_, v_____do__lift_1826_);
lean_dec(v_i_1821_);
return v_res_1827_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg(lean_object* v_inst_1828_, lean_object* v_inst_1829_, lean_object* v_args_1830_, lean_object* v_endIdx_1831_, lean_object* v_b_1832_, lean_object* v_i_1833_){
_start:
{
lean_object* v_toApplicative_1834_; lean_object* v_toBind_1835_; lean_object* v_toPure_1836_; uint8_t v___x_1837_; 
v_toApplicative_1834_ = lean_ctor_get(v_inst_1829_, 0);
v_toBind_1835_ = lean_ctor_get(v_inst_1829_, 1);
lean_inc(v_toBind_1835_);
v_toPure_1836_ = lean_ctor_get(v_toApplicative_1834_, 1);
v___x_1837_ = lean_nat_dec_le(v_endIdx_1831_, v_i_1833_);
if (v___x_1837_ == 0)
{
lean_object* v___f_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; 
lean_inc_ref(v_args_1830_);
lean_inc_ref(v_inst_1829_);
lean_inc_ref(v_inst_1828_);
lean_inc(v_i_1833_);
v___f_1838_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1838_, 0, v_i_1833_);
lean_closure_set(v___f_1838_, 1, v_inst_1828_);
lean_closure_set(v___f_1838_, 2, v_inst_1829_);
lean_closure_set(v___f_1838_, 3, v_args_1830_);
lean_closure_set(v___f_1838_, 4, v_endIdx_1831_);
v___x_1839_ = l_Lean_instInhabitedExpr;
v___x_1840_ = lean_array_get(v___x_1839_, v_args_1830_, v_i_1833_);
lean_dec(v_i_1833_);
lean_dec_ref(v_args_1830_);
v___x_1841_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1828_, v_inst_1829_, v_b_1832_, v___x_1840_);
v___x_1842_ = lean_apply_4(v_toBind_1835_, lean_box(0), lean_box(0), v___x_1841_, v___f_1838_);
return v___x_1842_;
}
else
{
lean_object* v___x_1843_; 
lean_inc(v_toPure_1836_);
lean_dec(v_toBind_1835_);
lean_dec(v_i_1833_);
lean_dec(v_endIdx_1831_);
lean_dec_ref(v_args_1830_);
lean_dec_ref(v_inst_1829_);
lean_dec_ref(v_inst_1828_);
v___x_1843_ = lean_apply_2(v_toPure_1836_, lean_box(0), v_b_1832_);
return v___x_1843_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg___lam__0(lean_object* v_i_1844_, lean_object* v_inst_1845_, lean_object* v_inst_1846_, lean_object* v_args_1847_, lean_object* v_endIdx_1848_, lean_object* v_____do__lift_1849_){
_start:
{
lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; 
v___x_1850_ = lean_unsigned_to_nat(1u);
v___x_1851_ = lean_nat_add(v_i_1844_, v___x_1850_);
v___x_1852_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg(v_inst_1845_, v_inst_1846_, v_args_1847_, v_endIdx_1848_, v_____do__lift_1849_, v___x_1851_);
return v___x_1852_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go(lean_object* v_m_1853_, lean_object* v_inst_1854_, lean_object* v_inst_1855_, lean_object* v_args_1856_, lean_object* v_endIdx_1857_, lean_object* v_b_1858_, lean_object* v_i_1859_){
_start:
{
lean_object* v___x_1860_; 
v___x_1860_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg(v_inst_1854_, v_inst_1855_, v_args_1856_, v_endIdx_1857_, v_b_1858_, v_i_1859_);
return v___x_1860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRangeS___redArg(lean_object* v_inst_1861_, lean_object* v_inst_1862_, lean_object* v_f_1863_, lean_object* v_beginIdx_1864_, lean_object* v_endIdx_1865_, lean_object* v_args_1866_){
_start:
{
lean_object* v___x_1867_; 
v___x_1867_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg(v_inst_1861_, v_inst_1862_, v_args_1866_, v_endIdx_1865_, v_f_1863_, v_beginIdx_1864_);
return v___x_1867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRangeS(lean_object* v_m_1868_, lean_object* v_inst_1869_, lean_object* v_inst_1870_, lean_object* v_f_1871_, lean_object* v_beginIdx_1872_, lean_object* v_endIdx_1873_, lean_object* v_args_1874_){
_start:
{
lean_object* v___x_1875_; 
v___x_1875_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg(v_inst_1869_, v_inst_1870_, v_args_1874_, v_endIdx_1873_, v_f_1871_, v_beginIdx_1872_);
return v___x_1875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___redArg(lean_object* v_inst_1876_, lean_object* v_inst_1877_, lean_object* v_f_1878_, lean_object* v_args_1879_){
_start:
{
lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; 
v___x_1880_ = lean_unsigned_to_nat(0u);
v___x_1881_ = lean_array_get_size(v_args_1879_);
v___x_1882_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg(v_inst_1876_, v_inst_1877_, v_args_1879_, v___x_1881_, v_f_1878_, v___x_1880_);
return v___x_1882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS(lean_object* v_m_1883_, lean_object* v_inst_1884_, lean_object* v_inst_1885_, lean_object* v_f_1886_, lean_object* v_args_1887_){
_start:
{
lean_object* v___x_1888_; 
v___x_1888_ = l_Lean_Meta_Sym_Internal_mkAppNS___redArg(v_inst_1884_, v_inst_1885_, v_f_1886_, v_args_1887_);
return v___x_1888_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg___lam__0___boxed(lean_object* v_inst_1889_, lean_object* v_inst_1890_, lean_object* v_revArgs_1891_, lean_object* v_start_1892_, lean_object* v_i_1893_, lean_object* v_____do__lift_1894_){
_start:
{
lean_object* v_res_1895_; 
v_res_1895_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg___lam__0(v_inst_1889_, v_inst_1890_, v_revArgs_1891_, v_start_1892_, v_i_1893_, v_____do__lift_1894_);
lean_dec(v_i_1893_);
return v_res_1895_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg(lean_object* v_inst_1896_, lean_object* v_inst_1897_, lean_object* v_revArgs_1898_, lean_object* v_start_1899_, lean_object* v_b_1900_, lean_object* v_i_1901_){
_start:
{
lean_object* v_toApplicative_1902_; lean_object* v_toBind_1903_; lean_object* v_toPure_1904_; uint8_t v___x_1905_; 
v_toApplicative_1902_ = lean_ctor_get(v_inst_1897_, 0);
v_toBind_1903_ = lean_ctor_get(v_inst_1897_, 1);
lean_inc(v_toBind_1903_);
v_toPure_1904_ = lean_ctor_get(v_toApplicative_1902_, 1);
v___x_1905_ = lean_nat_dec_le(v_i_1901_, v_start_1899_);
if (v___x_1905_ == 0)
{
lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v_i_1908_; lean_object* v___f_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; 
v___x_1906_ = l_Lean_instInhabitedExpr;
v___x_1907_ = lean_unsigned_to_nat(1u);
v_i_1908_ = lean_nat_sub(v_i_1901_, v___x_1907_);
lean_inc(v_i_1908_);
lean_inc_ref(v_revArgs_1898_);
lean_inc_ref(v_inst_1897_);
lean_inc_ref(v_inst_1896_);
v___f_1909_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1909_, 0, v_inst_1896_);
lean_closure_set(v___f_1909_, 1, v_inst_1897_);
lean_closure_set(v___f_1909_, 2, v_revArgs_1898_);
lean_closure_set(v___f_1909_, 3, v_start_1899_);
lean_closure_set(v___f_1909_, 4, v_i_1908_);
v___x_1910_ = lean_array_get(v___x_1906_, v_revArgs_1898_, v_i_1908_);
lean_dec(v_i_1908_);
lean_dec_ref(v_revArgs_1898_);
v___x_1911_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1896_, v_inst_1897_, v_b_1900_, v___x_1910_);
v___x_1912_ = lean_apply_4(v_toBind_1903_, lean_box(0), lean_box(0), v___x_1911_, v___f_1909_);
return v___x_1912_;
}
else
{
lean_object* v___x_1913_; 
lean_inc(v_toPure_1904_);
lean_dec(v_toBind_1903_);
lean_dec(v_start_1899_);
lean_dec_ref(v_revArgs_1898_);
lean_dec_ref(v_inst_1897_);
lean_dec_ref(v_inst_1896_);
v___x_1913_ = lean_apply_2(v_toPure_1904_, lean_box(0), v_b_1900_);
return v___x_1913_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg___lam__0(lean_object* v_inst_1914_, lean_object* v_inst_1915_, lean_object* v_revArgs_1916_, lean_object* v_start_1917_, lean_object* v_i_1918_, lean_object* v_____do__lift_1919_){
_start:
{
lean_object* v___x_1920_; 
v___x_1920_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg(v_inst_1914_, v_inst_1915_, v_revArgs_1916_, v_start_1917_, v_____do__lift_1919_, v_i_1918_);
return v___x_1920_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg___boxed(lean_object* v_inst_1921_, lean_object* v_inst_1922_, lean_object* v_revArgs_1923_, lean_object* v_start_1924_, lean_object* v_b_1925_, lean_object* v_i_1926_){
_start:
{
lean_object* v_res_1927_; 
v_res_1927_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg(v_inst_1921_, v_inst_1922_, v_revArgs_1923_, v_start_1924_, v_b_1925_, v_i_1926_);
lean_dec(v_i_1926_);
return v_res_1927_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go(lean_object* v_m_1928_, lean_object* v_inst_1929_, lean_object* v_inst_1930_, lean_object* v_revArgs_1931_, lean_object* v_start_1932_, lean_object* v_b_1933_, lean_object* v_i_1934_){
_start:
{
lean_object* v___x_1935_; 
v___x_1935_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg(v_inst_1929_, v_inst_1930_, v_revArgs_1931_, v_start_1932_, v_b_1933_, v_i_1934_);
return v___x_1935_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___boxed(lean_object* v_m_1936_, lean_object* v_inst_1937_, lean_object* v_inst_1938_, lean_object* v_revArgs_1939_, lean_object* v_start_1940_, lean_object* v_b_1941_, lean_object* v_i_1942_){
_start:
{
lean_object* v_res_1943_; 
v_res_1943_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go(v_m_1936_, v_inst_1937_, v_inst_1938_, v_revArgs_1939_, v_start_1940_, v_b_1941_, v_i_1942_);
lean_dec(v_i_1942_);
return v_res_1943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevRangeS___redArg(lean_object* v_inst_1944_, lean_object* v_inst_1945_, lean_object* v_f_1946_, lean_object* v_beginIdx_1947_, lean_object* v_endIdx_1948_, lean_object* v_revArgs_1949_){
_start:
{
lean_object* v___x_1950_; 
v___x_1950_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg(v_inst_1944_, v_inst_1945_, v_revArgs_1949_, v_beginIdx_1947_, v_f_1946_, v_endIdx_1948_);
return v___x_1950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevRangeS___redArg___boxed(lean_object* v_inst_1951_, lean_object* v_inst_1952_, lean_object* v_f_1953_, lean_object* v_beginIdx_1954_, lean_object* v_endIdx_1955_, lean_object* v_revArgs_1956_){
_start:
{
lean_object* v_res_1957_; 
v_res_1957_ = l_Lean_Meta_Sym_Internal_mkAppRevRangeS___redArg(v_inst_1951_, v_inst_1952_, v_f_1953_, v_beginIdx_1954_, v_endIdx_1955_, v_revArgs_1956_);
lean_dec(v_endIdx_1955_);
return v_res_1957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevRangeS(lean_object* v_m_1958_, lean_object* v_inst_1959_, lean_object* v_inst_1960_, lean_object* v_f_1961_, lean_object* v_beginIdx_1962_, lean_object* v_endIdx_1963_, lean_object* v_revArgs_1964_){
_start:
{
lean_object* v___x_1965_; 
v___x_1965_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg(v_inst_1959_, v_inst_1960_, v_revArgs_1964_, v_beginIdx_1962_, v_f_1961_, v_endIdx_1963_);
return v___x_1965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevRangeS___boxed(lean_object* v_m_1966_, lean_object* v_inst_1967_, lean_object* v_inst_1968_, lean_object* v_f_1969_, lean_object* v_beginIdx_1970_, lean_object* v_endIdx_1971_, lean_object* v_revArgs_1972_){
_start:
{
lean_object* v_res_1973_; 
v_res_1973_ = l_Lean_Meta_Sym_Internal_mkAppRevRangeS(v_m_1966_, v_inst_1967_, v_inst_1968_, v_f_1969_, v_beginIdx_1970_, v_endIdx_1971_, v_revArgs_1972_);
lean_dec(v_endIdx_1971_);
return v_res_1973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevS___redArg(lean_object* v_inst_1974_, lean_object* v_inst_1975_, lean_object* v_f_1976_, lean_object* v_revArgs_1977_){
_start:
{
lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; 
v___x_1978_ = lean_unsigned_to_nat(0u);
v___x_1979_ = lean_array_get_size(v_revArgs_1977_);
v___x_1980_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg(v_inst_1974_, v_inst_1975_, v_revArgs_1977_, v___x_1978_, v_f_1976_, v___x_1979_);
return v___x_1980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevS(lean_object* v_m_1981_, lean_object* v_inst_1982_, lean_object* v_inst_1983_, lean_object* v_f_1984_, lean_object* v_revArgs_1985_){
_start:
{
lean_object* v___x_1986_; 
v___x_1986_ = l_Lean_Meta_Sym_Internal_mkAppRevS___redArg(v_inst_1982_, v_inst_1983_, v_f_1984_, v_revArgs_1985_);
return v___x_1986_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
