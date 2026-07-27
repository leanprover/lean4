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
size_t v_x_2192__boxed_191_; size_t v_x_2193__boxed_192_; lean_object* v_res_193_; 
v_x_2192__boxed_191_ = lean_unbox_usize(v_x_187_);
lean_dec(v_x_187_);
v_x_2193__boxed_192_ = lean_unbox_usize(v_x_188_);
lean_dec(v_x_188_);
v_res_193_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg(v_x_186_, v_x_2192__boxed_191_, v_x_2193__boxed_192_, v_x_189_, v_x_190_);
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
lean_dec(v_i_202_);
lean_inc_ref(v_k_u2080_204_);
return v_k_u2080_204_;
}
else
{
lean_object* v_k_x27_207_; uint8_t v___x_208_; 
v_k_x27_207_ = lean_array_fget_borrowed(v_keys_201_, v_i_202_);
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
lean_dec_ref(v_k_214_);
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
v___x_222_ = lean_box(2);
v___x_223_ = ((size_t)31ULL);
v___x_224_ = lean_usize_land(v_x_218_, v___x_223_);
v_j_225_ = lean_usize_to_nat(v___x_224_);
v___x_226_ = lean_array_get_borrowed(v___x_222_, v_es_221_, v_j_225_);
lean_dec(v_j_225_);
switch(lean_obj_tag(v___x_226_))
{
case 0:
{
lean_object* v_key_227_; uint8_t v___x_228_; 
v_key_227_ = lean_ctor_get(v___x_226_, 0);
v___x_228_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_219_, v_key_227_);
if (v___x_228_ == 0)
{
lean_inc_ref(v_x_220_);
return v_x_220_;
}
else
{
lean_inc(v_key_227_);
return v_key_227_;
}
}
case 1:
{
lean_object* v_node_229_; size_t v___x_230_; size_t v___x_231_; 
v_node_229_ = lean_ctor_get(v___x_226_, 0);
v___x_230_ = ((size_t)5ULL);
v___x_231_ = lean_usize_shift_right(v_x_218_, v___x_230_);
v_x_217_ = v_node_229_;
v_x_218_ = v___x_231_;
goto _start;
}
default: 
{
lean_inc_ref(v_x_220_);
return v_x_220_;
}
}
}
else
{
lean_object* v_ks_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v_ks_233_ = lean_ctor_get(v_x_217_, 0);
v___x_234_ = lean_unsigned_to_nat(0u);
v___x_235_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0___redArg(v_ks_233_, v___x_234_, v_x_219_, v_x_220_);
return v___x_235_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg___boxed(lean_object* v_x_236_, lean_object* v_x_237_, lean_object* v_x_238_, lean_object* v_x_239_){
_start:
{
size_t v_x_2374__boxed_240_; lean_object* v_res_241_; 
v_x_2374__boxed_240_ = lean_unbox_usize(v_x_237_);
lean_dec(v_x_237_);
v_res_241_ = l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg(v_x_236_, v_x_2374__boxed_240_, v_x_238_, v_x_239_);
lean_dec_ref(v_x_239_);
lean_dec_ref(v_x_238_);
lean_dec_ref(v_x_236_);
return v_res_241_;
}
}
static size_t _init_l_Lean_Meta_Sym_Internal_Sym_share1___redArg___closed__0(void){
_start:
{
lean_object* v___x_242_; size_t v___x_243_; 
v___x_242_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy;
v___x_243_ = lean_ptr_addr(v___x_242_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object* v_e_244_, lean_object* v_a_245_){
_start:
{
lean_object* v___x_247_; lean_object* v_share_248_; lean_object* v___x_249_; uint64_t v___x_250_; size_t v___x_251_; lean_object* v___x_252_; size_t v___x_253_; size_t v___x_254_; uint8_t v___x_255_; 
v___x_247_ = lean_st_ref_get(v_a_245_);
v_share_248_ = lean_ctor_get(v___x_247_, 0);
lean_inc_ref(v_share_248_);
lean_dec(v___x_247_);
v___x_249_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy;
v___x_250_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_244_);
v___x_251_ = lean_uint64_to_usize(v___x_250_);
v___x_252_ = l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg(v_share_248_, v___x_251_, v_e_244_, v___x_249_);
lean_dec_ref(v_share_248_);
v___x_253_ = lean_ptr_addr(v___x_252_);
v___x_254_ = lean_usize_once(&l_Lean_Meta_Sym_Internal_Sym_share1___redArg___closed__0, &l_Lean_Meta_Sym_Internal_Sym_share1___redArg___closed__0_once, _init_l_Lean_Meta_Sym_Internal_Sym_share1___redArg___closed__0);
v___x_255_ = lean_usize_dec_eq(v___x_253_, v___x_254_);
if (v___x_255_ == 0)
{
lean_object* v___x_256_; 
lean_dec_ref(v_e_244_);
v___x_256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_256_, 0, v___x_252_);
return v___x_256_;
}
else
{
lean_object* v___x_257_; lean_object* v_share_258_; lean_object* v_maxFVar_259_; lean_object* v_proofInstInfo_260_; lean_object* v_inferType_261_; lean_object* v_getLevel_262_; lean_object* v_congrInfo_263_; lean_object* v_defEqI_264_; lean_object* v_extensions_265_; lean_object* v_issues_266_; lean_object* v_canon_267_; lean_object* v_instanceOverrides_268_; uint8_t v_debug_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_280_; 
lean_dec_ref(v___x_252_);
v___x_257_ = lean_st_ref_take(v_a_245_);
v_share_258_ = lean_ctor_get(v___x_257_, 0);
v_maxFVar_259_ = lean_ctor_get(v___x_257_, 1);
v_proofInstInfo_260_ = lean_ctor_get(v___x_257_, 2);
v_inferType_261_ = lean_ctor_get(v___x_257_, 3);
v_getLevel_262_ = lean_ctor_get(v___x_257_, 4);
v_congrInfo_263_ = lean_ctor_get(v___x_257_, 5);
v_defEqI_264_ = lean_ctor_get(v___x_257_, 6);
v_extensions_265_ = lean_ctor_get(v___x_257_, 7);
v_issues_266_ = lean_ctor_get(v___x_257_, 8);
v_canon_267_ = lean_ctor_get(v___x_257_, 9);
v_instanceOverrides_268_ = lean_ctor_get(v___x_257_, 10);
v_debug_269_ = lean_ctor_get_uint8(v___x_257_, sizeof(void*)*11);
v_isSharedCheck_280_ = !lean_is_exclusive(v___x_257_);
if (v_isSharedCheck_280_ == 0)
{
v___x_271_ = v___x_257_;
v_isShared_272_ = v_isSharedCheck_280_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_instanceOverrides_268_);
lean_inc(v_canon_267_);
lean_inc(v_issues_266_);
lean_inc(v_extensions_265_);
lean_inc(v_defEqI_264_);
lean_inc(v_congrInfo_263_);
lean_inc(v_getLevel_262_);
lean_inc(v_inferType_261_);
lean_inc(v_proofInstInfo_260_);
lean_inc(v_maxFVar_259_);
lean_inc(v_share_258_);
lean_dec(v___x_257_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_280_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_276_; 
v___x_273_ = lean_box(0);
lean_inc_ref(v_e_244_);
v___x_274_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1___redArg(v_share_258_, v_e_244_, v___x_273_);
if (v_isShared_272_ == 0)
{
lean_ctor_set(v___x_271_, 0, v___x_274_);
v___x_276_ = v___x_271_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v___x_274_);
lean_ctor_set(v_reuseFailAlloc_279_, 1, v_maxFVar_259_);
lean_ctor_set(v_reuseFailAlloc_279_, 2, v_proofInstInfo_260_);
lean_ctor_set(v_reuseFailAlloc_279_, 3, v_inferType_261_);
lean_ctor_set(v_reuseFailAlloc_279_, 4, v_getLevel_262_);
lean_ctor_set(v_reuseFailAlloc_279_, 5, v_congrInfo_263_);
lean_ctor_set(v_reuseFailAlloc_279_, 6, v_defEqI_264_);
lean_ctor_set(v_reuseFailAlloc_279_, 7, v_extensions_265_);
lean_ctor_set(v_reuseFailAlloc_279_, 8, v_issues_266_);
lean_ctor_set(v_reuseFailAlloc_279_, 9, v_canon_267_);
lean_ctor_set(v_reuseFailAlloc_279_, 10, v_instanceOverrides_268_);
lean_ctor_set_uint8(v_reuseFailAlloc_279_, sizeof(void*)*11, v_debug_269_);
v___x_276_ = v_reuseFailAlloc_279_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_277_ = lean_st_ref_set(v_a_245_, v___x_276_);
v___x_278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_278_, 0, v_e_244_);
return v___x_278_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg___boxed(lean_object* v_e_281_, lean_object* v_a_282_, lean_object* v_a_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v_e_281_, v_a_282_);
lean_dec(v_a_282_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Sym_share1(lean_object* v_e_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v_e_285_, v_a_287_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___boxed(lean_object* v_e_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Lean_Meta_Sym_Internal_Sym_share1(v_e_294_, v_a_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_);
lean_dec(v_a_300_);
lean_dec_ref(v_a_299_);
lean_dec(v_a_298_);
lean_dec_ref(v_a_297_);
lean_dec(v_a_296_);
lean_dec_ref(v_a_295_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0(lean_object* v_00_u03b2_303_, lean_object* v_x_304_, size_t v_x_305_, lean_object* v_x_306_, lean_object* v_x_307_){
_start:
{
lean_object* v___x_308_; 
v___x_308_ = l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg(v_x_304_, v_x_305_, v_x_306_, v_x_307_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___boxed(lean_object* v_00_u03b2_309_, lean_object* v_x_310_, lean_object* v_x_311_, lean_object* v_x_312_, lean_object* v_x_313_){
_start:
{
size_t v_x_2472__boxed_314_; lean_object* v_res_315_; 
v_x_2472__boxed_314_ = lean_unbox_usize(v_x_311_);
lean_dec(v_x_311_);
v_res_315_ = l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0(v_00_u03b2_309_, v_x_310_, v_x_2472__boxed_314_, v_x_312_, v_x_313_);
lean_dec_ref(v_x_313_);
lean_dec_ref(v_x_312_);
lean_dec_ref(v_x_310_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1(lean_object* v_00_u03b2_316_, lean_object* v_x_317_, lean_object* v_x_318_, lean_object* v_x_319_){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1___redArg(v_x_317_, v_x_318_, v_x_319_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0(lean_object* v_00_u03b2_321_, lean_object* v_keys_322_, lean_object* v_vals_323_, lean_object* v_heq_324_, lean_object* v_i_325_, lean_object* v_k_326_, lean_object* v_k_u2080_327_){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0___redArg(v_keys_322_, v_i_325_, v_k_326_, v_k_u2080_327_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0___boxed(lean_object* v_00_u03b2_329_, lean_object* v_keys_330_, lean_object* v_vals_331_, lean_object* v_heq_332_, lean_object* v_i_333_, lean_object* v_k_334_, lean_object* v_k_u2080_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0(v_00_u03b2_329_, v_keys_330_, v_vals_331_, v_heq_332_, v_i_333_, v_k_334_, v_k_u2080_335_);
lean_dec_ref(v_k_u2080_335_);
lean_dec_ref(v_k_334_);
lean_dec_ref(v_vals_331_);
lean_dec_ref(v_keys_330_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2(lean_object* v_00_u03b2_337_, lean_object* v_x_338_, size_t v_x_339_, size_t v_x_340_, lean_object* v_x_341_, lean_object* v_x_342_){
_start:
{
lean_object* v___x_343_; 
v___x_343_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg(v_x_338_, v_x_339_, v_x_340_, v_x_341_, v_x_342_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_344_, lean_object* v_x_345_, lean_object* v_x_346_, lean_object* v_x_347_, lean_object* v_x_348_, lean_object* v_x_349_){
_start:
{
size_t v_x_2496__boxed_350_; size_t v_x_2497__boxed_351_; lean_object* v_res_352_; 
v_x_2496__boxed_350_ = lean_unbox_usize(v_x_346_);
lean_dec(v_x_346_);
v_x_2497__boxed_351_ = lean_unbox_usize(v_x_347_);
lean_dec(v_x_347_);
v_res_352_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2(v_00_u03b2_344_, v_x_345_, v_x_2496__boxed_350_, v_x_2497__boxed_351_, v_x_348_, v_x_349_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_353_, lean_object* v_n_354_, lean_object* v_k_355_, lean_object* v_v_356_){
_start:
{
lean_object* v___x_357_; 
v___x_357_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__3___redArg(v_n_354_, v_k_355_, v_v_356_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_358_, size_t v_depth_359_, lean_object* v_keys_360_, lean_object* v_vals_361_, lean_object* v_heq_362_, lean_object* v_i_363_, lean_object* v_entries_364_){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4___redArg(v_depth_359_, v_keys_360_, v_vals_361_, v_i_363_, v_entries_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_366_, lean_object* v_depth_367_, lean_object* v_keys_368_, lean_object* v_vals_369_, lean_object* v_heq_370_, lean_object* v_i_371_, lean_object* v_entries_372_){
_start:
{
size_t v_depth_boxed_373_; lean_object* v_res_374_; 
v_depth_boxed_373_ = lean_unbox_usize(v_depth_367_);
lean_dec(v_depth_367_);
v_res_374_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4(v_00_u03b2_366_, v_depth_boxed_373_, v_keys_368_, v_vals_369_, v_heq_370_, v_i_371_, v_entries_372_);
lean_dec_ref(v_vals_369_);
lean_dec_ref(v_keys_368_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_375_, lean_object* v_x_376_, lean_object* v_x_377_, lean_object* v_x_378_, lean_object* v_x_379_){
_start:
{
lean_object* v___x_380_; 
v___x_380_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__3_spec__4___redArg(v_x_376_, v_x_377_, v_x_378_, v_x_379_);
return v___x_380_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0(void){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = l_Lean_Meta_Sym_instInhabitedSymM(lean_box(0));
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0(lean_object* v_msg_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
lean_object* v___x_390_; lean_object* v___x_780__overap_391_; lean_object* v___x_392_; 
v___x_390_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0, &l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0);
v___x_780__overap_391_ = lean_panic_fn_borrowed(v___x_390_, v_msg_382_);
lean_inc(v___y_388_);
lean_inc_ref(v___y_387_);
lean_inc(v___y_386_);
lean_inc_ref(v___y_385_);
lean_inc(v___y_384_);
lean_inc_ref(v___y_383_);
v___x_392_ = lean_apply_7(v___x_780__overap_391_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, lean_box(0));
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___boxed(lean_object* v_msg_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0(v_msg_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_);
lean_dec(v___y_399_);
lean_dec_ref(v___y_398_);
lean_dec(v___y_397_);
lean_dec_ref(v___y_396_);
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
return v_res_401_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__3(void){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_405_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__2));
v___x_406_ = lean_unsigned_to_nat(2u);
v___x_407_ = lean_unsigned_to_nat(42u);
v___x_408_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__1));
v___x_409_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_410_ = l_mkPanicMessageWithDecl(v___x_409_, v___x_408_, v___x_407_, v___x_406_, v___x_405_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object* v_e_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_){
_start:
{
lean_object* v___x_419_; lean_object* v_share_420_; lean_object* v___x_421_; uint64_t v___x_422_; size_t v___x_423_; lean_object* v___x_424_; size_t v___x_425_; size_t v___x_426_; uint8_t v___x_427_; 
v___x_419_ = lean_st_ref_get(v_a_413_);
v_share_420_ = lean_ctor_get(v___x_419_, 0);
lean_inc_ref(v_share_420_);
lean_dec(v___x_419_);
v___x_421_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy;
v___x_422_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_411_);
v___x_423_ = lean_uint64_to_usize(v___x_422_);
v___x_424_ = l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg(v_share_420_, v___x_423_, v_e_411_, v___x_421_);
lean_dec_ref(v_share_420_);
v___x_425_ = lean_ptr_addr(v___x_424_);
lean_dec_ref(v___x_424_);
v___x_426_ = lean_ptr_addr(v_e_411_);
v___x_427_ = lean_usize_dec_eq(v___x_425_, v___x_426_);
if (v___x_427_ == 0)
{
lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_428_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__3, &l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__3_once, _init_l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__3);
v___x_429_ = l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0(v___x_428_, v_a_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_);
return v___x_429_;
}
else
{
lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_430_ = lean_box(0);
v___x_431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_431_, 0, v___x_430_);
return v___x_431_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared___boxed(lean_object* v_e_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_e_432_, v_a_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_, v_a_438_);
lean_dec(v_a_438_);
lean_dec_ref(v_a_437_);
lean_dec(v_a_436_);
lean_dec_ref(v_a_435_);
lean_dec(v_a_434_);
lean_dec_ref(v_a_433_);
lean_dec_ref(v_e_432_);
return v_res_440_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__0(void){
_start:
{
lean_object* v___x_449_; 
v___x_449_ = l_Lean_Meta_Sym_instInhabitedSymM(lean_box(0));
return v___x_449_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__3(void){
_start:
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_452_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2));
v___x_453_ = lean_unsigned_to_nat(16u);
v___x_454_ = lean_unsigned_to_nat(62u);
v___x_455_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__1));
v___x_456_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_457_ = l_mkPanicMessageWithDecl(v___x_456_, v___x_455_, v___x_454_, v___x_453_, v___x_452_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM___redArg(lean_object* v_k_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_){
_start:
{
lean_object* v___x_466_; lean_object* v___x_467_; uint8_t v_debug_468_; lean_object* v_env_469_; lean_object* v___x_470_; lean_object* v___x_471_; uint8_t v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_466_ = lean_st_ref_get(v_a_460_);
v___x_467_ = lean_st_ref_get(v_a_464_);
v_debug_468_ = lean_ctor_get_uint8(v___x_466_, sizeof(void*)*11);
lean_dec(v___x_466_);
v_env_469_ = lean_ctor_get(v___x_467_, 0);
lean_inc_ref(v_env_469_);
lean_dec(v___x_467_);
v___x_470_ = lean_box(v_debug_468_);
v___x_471_ = lean_apply_1(v_k_458_, v___x_470_);
v___x_472_ = 0;
v___x_473_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_473_, 0, v_env_469_);
lean_ctor_set_uint8(v___x_473_, sizeof(void*)*1, v___x_472_);
lean_ctor_set_uint8(v___x_473_, sizeof(void*)*1 + 1, v___x_472_);
v___x_474_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___x_471_, v___x_473_, v_a_460_);
if (lean_obj_tag(v___x_474_) == 0)
{
lean_object* v_a_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_487_; 
v_a_475_ = lean_ctor_get(v___x_474_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_474_);
if (v_isSharedCheck_487_ == 0)
{
v___x_477_ = v___x_474_;
v_isShared_478_ = v_isSharedCheck_487_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_a_475_);
lean_dec(v___x_474_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_487_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
if (lean_obj_tag(v_a_475_) == 0)
{
lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_1305__overap_481_; lean_object* v___x_482_; 
lean_dec_ref_known(v_a_475_, 1);
lean_del_object(v___x_477_);
v___x_479_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__0, &l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__0_once, _init_l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__0);
v___x_480_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__3, &l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__3_once, _init_l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__3);
v___x_1305__overap_481_ = l_panic___redArg(v___x_479_, v___x_480_);
lean_inc(v_a_464_);
lean_inc_ref(v_a_463_);
lean_inc(v_a_462_);
lean_inc_ref(v_a_461_);
lean_inc(v_a_460_);
lean_inc_ref(v_a_459_);
v___x_482_ = lean_apply_7(v___x_1305__overap_481_, v_a_459_, v_a_460_, v_a_461_, v_a_462_, v_a_463_, v_a_464_, lean_box(0));
return v___x_482_;
}
else
{
lean_object* v_a_483_; lean_object* v___x_485_; 
v_a_483_ = lean_ctor_get(v_a_475_, 0);
lean_inc(v_a_483_);
lean_dec_ref_known(v_a_475_, 1);
if (v_isShared_478_ == 0)
{
lean_ctor_set(v___x_477_, 0, v_a_483_);
v___x_485_ = v___x_477_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v_a_483_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
}
}
else
{
lean_object* v_a_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_495_; 
v_a_488_ = lean_ctor_get(v___x_474_, 0);
v_isSharedCheck_495_ = !lean_is_exclusive(v___x_474_);
if (v_isSharedCheck_495_ == 0)
{
v___x_490_ = v___x_474_;
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_a_488_);
lean_dec(v___x_474_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___x_493_; 
if (v_isShared_491_ == 0)
{
v___x_493_ = v___x_490_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_a_488_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___boxed(lean_object* v_k_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l_Lean_Meta_Sym_Internal_liftBuilderM___redArg(v_k_496_, v_a_497_, v_a_498_, v_a_499_, v_a_500_, v_a_501_, v_a_502_);
lean_dec(v_a_502_);
lean_dec_ref(v_a_501_);
lean_dec(v_a_500_);
lean_dec_ref(v_a_499_);
lean_dec(v_a_498_);
lean_dec_ref(v_a_497_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM(lean_object* v_00_u03b1_505_, lean_object* v_k_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_){
_start:
{
lean_object* v___x_514_; lean_object* v___x_515_; uint8_t v_debug_516_; lean_object* v_env_517_; lean_object* v___x_518_; lean_object* v___x_519_; uint8_t v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_514_ = lean_st_ref_get(v_a_508_);
v___x_515_ = lean_st_ref_get(v_a_512_);
v_debug_516_ = lean_ctor_get_uint8(v___x_514_, sizeof(void*)*11);
lean_dec(v___x_514_);
v_env_517_ = lean_ctor_get(v___x_515_, 0);
lean_inc_ref(v_env_517_);
lean_dec(v___x_515_);
v___x_518_ = lean_box(v_debug_516_);
v___x_519_ = lean_apply_1(v_k_506_, v___x_518_);
v___x_520_ = 0;
v___x_521_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_521_, 0, v_env_517_);
lean_ctor_set_uint8(v___x_521_, sizeof(void*)*1, v___x_520_);
lean_ctor_set_uint8(v___x_521_, sizeof(void*)*1 + 1, v___x_520_);
v___x_522_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___x_519_, v___x_521_, v_a_508_);
if (lean_obj_tag(v___x_522_) == 0)
{
lean_object* v_a_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_535_; 
v_a_523_ = lean_ctor_get(v___x_522_, 0);
v_isSharedCheck_535_ = !lean_is_exclusive(v___x_522_);
if (v_isSharedCheck_535_ == 0)
{
v___x_525_ = v___x_522_;
v_isShared_526_ = v_isSharedCheck_535_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_a_523_);
lean_dec(v___x_522_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_535_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
if (lean_obj_tag(v_a_523_) == 0)
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_1333__overap_529_; lean_object* v___x_530_; 
lean_dec_ref_known(v_a_523_, 1);
lean_del_object(v___x_525_);
v___x_527_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__0, &l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__0_once, _init_l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__0);
v___x_528_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__3, &l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__3_once, _init_l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__3);
v___x_1333__overap_529_ = l_panic___redArg(v___x_527_, v___x_528_);
lean_inc(v_a_512_);
lean_inc_ref(v_a_511_);
lean_inc(v_a_510_);
lean_inc_ref(v_a_509_);
lean_inc(v_a_508_);
lean_inc_ref(v_a_507_);
v___x_530_ = lean_apply_7(v___x_1333__overap_529_, v_a_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_, lean_box(0));
return v___x_530_;
}
else
{
lean_object* v_a_531_; lean_object* v___x_533_; 
v_a_531_ = lean_ctor_get(v_a_523_, 0);
lean_inc(v_a_531_);
lean_dec_ref_known(v_a_523_, 1);
if (v_isShared_526_ == 0)
{
lean_ctor_set(v___x_525_, 0, v_a_531_);
v___x_533_ = v___x_525_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v_a_531_);
v___x_533_ = v_reuseFailAlloc_534_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
return v___x_533_;
}
}
}
}
else
{
lean_object* v_a_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_543_; 
v_a_536_ = lean_ctor_get(v___x_522_, 0);
v_isSharedCheck_543_ = !lean_is_exclusive(v___x_522_);
if (v_isSharedCheck_543_ == 0)
{
v___x_538_ = v___x_522_;
v_isShared_539_ = v_isSharedCheck_543_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_a_536_);
lean_dec(v___x_522_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_543_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_541_; 
if (v_isShared_539_ == 0)
{
v___x_541_ = v___x_538_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v_a_536_);
v___x_541_ = v_reuseFailAlloc_542_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
return v___x_541_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM___boxed(lean_object* v_00_u03b1_544_, lean_object* v_k_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l_Lean_Meta_Sym_Internal_liftBuilderM(v_00_u03b1_544_, v_k_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_, v_a_550_, v_a_551_);
lean_dec(v_a_551_);
lean_dec_ref(v_a_550_);
lean_dec(v_a_549_);
lean_dec_ref(v_a_548_);
lean_dec(v_a_547_);
lean_dec_ref(v_a_546_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_share1___redArg(lean_object* v_e_554_, lean_object* v_a_555_){
_start:
{
lean_object* v___x_556_; uint64_t v___x_557_; size_t v___x_558_; lean_object* v___x_559_; size_t v___x_560_; size_t v___x_561_; uint8_t v___x_562_; 
v___x_556_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy;
v___x_557_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_554_);
v___x_558_ = lean_uint64_to_usize(v___x_557_);
v___x_559_ = l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg(v_a_555_, v___x_558_, v_e_554_, v___x_556_);
v___x_560_ = lean_ptr_addr(v___x_559_);
v___x_561_ = lean_usize_once(&l_Lean_Meta_Sym_Internal_Sym_share1___redArg___closed__0, &l_Lean_Meta_Sym_Internal_Sym_share1___redArg___closed__0_once, _init_l_Lean_Meta_Sym_Internal_Sym_share1___redArg___closed__0);
v___x_562_ = lean_usize_dec_eq(v___x_560_, v___x_561_);
if (v___x_562_ == 0)
{
lean_object* v___x_563_; 
lean_dec_ref(v_e_554_);
v___x_563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_563_, 0, v___x_559_);
lean_ctor_set(v___x_563_, 1, v_a_555_);
return v___x_563_;
}
else
{
lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
lean_dec_ref(v___x_559_);
v___x_564_ = lean_box(0);
lean_inc_ref(v_e_554_);
v___x_565_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1___redArg(v_a_555_, v_e_554_, v___x_564_);
v___x_566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_566_, 0, v_e_554_);
lean_ctor_set(v___x_566_, 1, v___x_565_);
return v___x_566_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_share1(lean_object* v_e_567_, uint8_t v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_){
_start:
{
lean_object* v___x_571_; 
v___x_571_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v_e_567_, v_a_570_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_share1___boxed(lean_object* v_e_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_){
_start:
{
uint8_t v_a_boxed_576_; lean_object* v_res_577_; 
v_a_boxed_576_ = lean_unbox(v_a_573_);
v_res_577_ = l_Lean_Meta_Sym_Internal_Builder_share1(v_e_572_, v_a_boxed_576_, v_a_574_, v_a_575_);
lean_dec_ref(v_a_574_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1(lean_object* v_msg_580_, uint8_t v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_){
_start:
{
lean_object* v___f_584_; lean_object* v___f_585_; lean_object* v___x_586_; lean_object* v___f_587_; lean_object* v___f_588_; lean_object* v___f_589_; lean_object* v___x_696__overap_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v___f_584_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__0));
v___f_585_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__1));
v___x_586_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___f_584_, v___f_585_);
v___f_587_ = lean_alloc_closure((void*)(l_EStateM_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_587_, 0, v___x_586_);
v___f_588_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_588_, 0, v___f_587_);
v___f_589_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_589_, 0, v___f_588_);
v___x_696__overap_590_ = lean_panic_fn_borrowed(v___f_589_, v_msg_580_);
lean_dec_ref(v___f_589_);
v___x_591_ = lean_box(v___y_581_);
lean_inc_ref(v___y_582_);
v___x_592_ = lean_apply_3(v___x_696__overap_590_, v___x_591_, v___y_582_, v___y_583_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___boxed(lean_object* v_msg_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_){
_start:
{
uint8_t v___y_798__boxed_597_; lean_object* v_res_598_; 
v___y_798__boxed_597_ = lean_unbox(v___y_594_);
v_res_598_ = l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1(v_msg_593_, v___y_798__boxed_597_, v___y_595_, v___y_596_);
lean_dec_ref(v___y_595_);
return v_res_598_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_599_, lean_object* v_i_600_, lean_object* v_k_601_){
_start:
{
lean_object* v___x_602_; uint8_t v___x_603_; 
v___x_602_ = lean_array_get_size(v_keys_599_);
v___x_603_ = lean_nat_dec_lt(v_i_600_, v___x_602_);
if (v___x_603_ == 0)
{
lean_dec(v_i_600_);
return v___x_603_;
}
else
{
lean_object* v_k_x27_604_; uint8_t v___x_605_; 
v_k_x27_604_ = lean_array_fget_borrowed(v_keys_599_, v_i_600_);
v___x_605_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_k_601_, v_k_x27_604_);
if (v___x_605_ == 0)
{
lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_606_ = lean_unsigned_to_nat(1u);
v___x_607_ = lean_nat_add(v_i_600_, v___x_606_);
lean_dec(v_i_600_);
v_i_600_ = v___x_607_;
goto _start;
}
else
{
lean_dec(v_i_600_);
return v___x_605_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_609_, lean_object* v_i_610_, lean_object* v_k_611_){
_start:
{
uint8_t v_res_612_; lean_object* v_r_613_; 
v_res_612_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg(v_keys_609_, v_i_610_, v_k_611_);
lean_dec_ref(v_k_611_);
lean_dec_ref(v_keys_609_);
v_r_613_ = lean_box(v_res_612_);
return v_r_613_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg(lean_object* v_x_614_, size_t v_x_615_, lean_object* v_x_616_){
_start:
{
if (lean_obj_tag(v_x_614_) == 0)
{
lean_object* v_es_617_; lean_object* v___x_618_; size_t v___x_619_; size_t v___x_620_; lean_object* v_j_621_; lean_object* v___x_622_; 
v_es_617_ = lean_ctor_get(v_x_614_, 0);
v___x_618_ = lean_box(2);
v___x_619_ = ((size_t)31ULL);
v___x_620_ = lean_usize_land(v_x_615_, v___x_619_);
v_j_621_ = lean_usize_to_nat(v___x_620_);
v___x_622_ = lean_array_get_borrowed(v___x_618_, v_es_617_, v_j_621_);
lean_dec(v_j_621_);
switch(lean_obj_tag(v___x_622_))
{
case 0:
{
lean_object* v_key_623_; uint8_t v___x_624_; 
v_key_623_ = lean_ctor_get(v___x_622_, 0);
v___x_624_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_616_, v_key_623_);
return v___x_624_;
}
case 1:
{
lean_object* v_node_625_; size_t v___x_626_; size_t v___x_627_; 
v_node_625_ = lean_ctor_get(v___x_622_, 0);
v___x_626_ = ((size_t)5ULL);
v___x_627_ = lean_usize_shift_right(v_x_615_, v___x_626_);
v_x_614_ = v_node_625_;
v_x_615_ = v___x_627_;
goto _start;
}
default: 
{
uint8_t v___x_629_; 
v___x_629_ = 0;
return v___x_629_;
}
}
}
else
{
lean_object* v_ks_630_; lean_object* v___x_631_; uint8_t v___x_632_; 
v_ks_630_ = lean_ctor_get(v_x_614_, 0);
v___x_631_ = lean_unsigned_to_nat(0u);
v___x_632_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg(v_ks_630_, v___x_631_, v_x_616_);
return v___x_632_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg___boxed(lean_object* v_x_633_, lean_object* v_x_634_, lean_object* v_x_635_){
_start:
{
size_t v_x_838__boxed_636_; uint8_t v_res_637_; lean_object* v_r_638_; 
v_x_838__boxed_636_ = lean_unbox_usize(v_x_634_);
lean_dec(v_x_634_);
v_res_637_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg(v_x_633_, v_x_838__boxed_636_, v_x_635_);
lean_dec_ref(v_x_635_);
lean_dec_ref(v_x_633_);
v_r_638_ = lean_box(v_res_637_);
return v_r_638_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg(lean_object* v_x_639_, lean_object* v_x_640_){
_start:
{
uint64_t v___x_641_; size_t v___x_642_; uint8_t v___x_643_; 
v___x_641_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_640_);
v___x_642_ = lean_uint64_to_usize(v___x_641_);
v___x_643_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg(v_x_639_, v___x_642_, v_x_640_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg___boxed(lean_object* v_x_644_, lean_object* v_x_645_){
_start:
{
uint8_t v_res_646_; lean_object* v_r_647_; 
v_res_646_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg(v_x_644_, v_x_645_);
lean_dec_ref(v_x_645_);
lean_dec_ref(v_x_644_);
v_r_647_ = lean_box(v_res_646_);
return v_r_647_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__2(void){
_start:
{
lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_650_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__1));
v___x_651_ = lean_unsigned_to_nat(2u);
v___x_652_ = lean_unsigned_to_nat(74u);
v___x_653_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__0));
v___x_654_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_655_ = l_mkPanicMessageWithDecl(v___x_654_, v___x_653_, v___x_652_, v___x_651_, v___x_650_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_assertShared(lean_object* v_e_656_, uint8_t v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_){
_start:
{
uint8_t v___x_660_; 
v___x_660_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg(v_a_659_, v_e_656_);
if (v___x_660_ == 0)
{
lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_661_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__2, &l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__2_once, _init_l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__2);
v___x_662_ = l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1(v___x_661_, v_a_657_, v_a_658_, v_a_659_);
return v___x_662_;
}
else
{
lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_663_ = lean_box(0);
v___x_664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_664_, 0, v___x_663_);
lean_ctor_set(v___x_664_, 1, v_a_659_);
return v___x_664_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_assertShared___boxed(lean_object* v_e_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_){
_start:
{
uint8_t v_a_boxed_669_; lean_object* v_res_670_; 
v_a_boxed_669_ = lean_unbox(v_a_666_);
v_res_670_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_e_665_, v_a_boxed_669_, v_a_667_, v_a_668_);
lean_dec_ref(v_a_667_);
lean_dec_ref(v_e_665_);
return v_res_670_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0(lean_object* v_00_u03b2_671_, lean_object* v_x_672_, lean_object* v_x_673_){
_start:
{
uint8_t v___x_674_; 
v___x_674_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg(v_x_672_, v_x_673_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___boxed(lean_object* v_00_u03b2_675_, lean_object* v_x_676_, lean_object* v_x_677_){
_start:
{
uint8_t v_res_678_; lean_object* v_r_679_; 
v_res_678_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0(v_00_u03b2_675_, v_x_676_, v_x_677_);
lean_dec_ref(v_x_677_);
lean_dec_ref(v_x_676_);
v_r_679_ = lean_box(v_res_678_);
return v_r_679_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0(lean_object* v_00_u03b2_680_, lean_object* v_x_681_, size_t v_x_682_, lean_object* v_x_683_){
_start:
{
uint8_t v___x_684_; 
v___x_684_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg(v_x_681_, v_x_682_, v_x_683_);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___boxed(lean_object* v_00_u03b2_685_, lean_object* v_x_686_, lean_object* v_x_687_, lean_object* v_x_688_){
_start:
{
size_t v_x_937__boxed_689_; uint8_t v_res_690_; lean_object* v_r_691_; 
v_x_937__boxed_689_ = lean_unbox_usize(v_x_687_);
lean_dec(v_x_687_);
v_res_690_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0(v_00_u03b2_685_, v_x_686_, v_x_937__boxed_689_, v_x_688_);
lean_dec_ref(v_x_688_);
lean_dec_ref(v_x_686_);
v_r_691_ = lean_box(v_res_690_);
return v_r_691_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_692_, lean_object* v_keys_693_, lean_object* v_vals_694_, lean_object* v_heq_695_, lean_object* v_i_696_, lean_object* v_k_697_){
_start:
{
uint8_t v___x_698_; 
v___x_698_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg(v_keys_693_, v_i_696_, v_k_697_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_699_, lean_object* v_keys_700_, lean_object* v_vals_701_, lean_object* v_heq_702_, lean_object* v_i_703_, lean_object* v_k_704_){
_start:
{
uint8_t v_res_705_; lean_object* v_r_706_; 
v_res_705_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2(v_00_u03b2_699_, v_keys_700_, v_vals_701_, v_heq_702_, v_i_703_, v_k_704_);
lean_dec_ref(v_k_704_);
lean_dec_ref(v_vals_701_);
lean_dec_ref(v_keys_700_);
v_r_706_ = lean_box(v_res_705_);
return v_r_706_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__10(void){
_start:
{
lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_726_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__9));
v___x_727_ = l_ReaderT_instMonad___redArg(v___x_726_);
return v___x_727_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__13(void){
_start:
{
lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_730_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__10, &l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__10_once, _init_l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__10);
v___x_731_ = lean_alloc_closure((void*)(l_ReaderT_read___boxed), 4, 3);
lean_closure_set(v___x_731_, 0, lean_box(0));
lean_closure_set(v___x_731_, 1, lean_box(0));
lean_closure_set(v___x_731_, 2, v___x_730_);
return v___x_731_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__14(void){
_start:
{
lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_732_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__13, &l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__13_once, _init_l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__13);
v___x_733_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__12));
v___x_734_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__11));
v___x_735_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_735_, 0, v___x_734_);
lean_ctor_set(v___x_735_, 1, v___x_733_);
lean_ctor_set(v___x_735_, 2, v___x_732_);
return v___x_735_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM(void){
_start:
{
lean_object* v___x_736_; 
v___x_736_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__14, &l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__14_once, _init_l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__14);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLitS___redArg(lean_object* v_inst_737_, lean_object* v_l_738_){
_start:
{
lean_object* v_share1_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
v_share1_739_ = lean_ctor_get(v_inst_737_, 0);
lean_inc(v_share1_739_);
lean_dec_ref(v_inst_737_);
v___x_740_ = l_Lean_Expr_lit___override(v_l_738_);
v___x_741_ = lean_apply_1(v_share1_739_, v___x_740_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLitS(lean_object* v_m_742_, lean_object* v_inst_743_, lean_object* v_l_744_){
_start:
{
lean_object* v___x_745_; 
v___x_745_ = l_Lean_Meta_Sym_Internal_mkLitS___redArg(v_inst_743_, v_l_744_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___redArg(lean_object* v_inst_746_, lean_object* v_declName_747_, lean_object* v_us_748_){
_start:
{
lean_object* v_share1_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
v_share1_749_ = lean_ctor_get(v_inst_746_, 0);
lean_inc(v_share1_749_);
lean_dec_ref(v_inst_746_);
v___x_750_ = l_Lean_Expr_const___override(v_declName_747_, v_us_748_);
v___x_751_ = lean_apply_1(v_share1_749_, v___x_750_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS(lean_object* v_m_752_, lean_object* v_inst_753_, lean_object* v_declName_754_, lean_object* v_us_755_){
_start:
{
lean_object* v___x_756_; 
v___x_756_ = l_Lean_Meta_Sym_Internal_mkConstS___redArg(v_inst_753_, v_declName_754_, v_us_755_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___redArg(lean_object* v_inst_757_, lean_object* v_idx_758_){
_start:
{
lean_object* v_share1_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v_share1_759_ = lean_ctor_get(v_inst_757_, 0);
lean_inc(v_share1_759_);
lean_dec_ref(v_inst_757_);
v___x_760_ = l_Lean_Expr_bvar___override(v_idx_758_);
v___x_761_ = lean_apply_1(v_share1_759_, v___x_760_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS(lean_object* v_m_762_, lean_object* v_inst_763_, lean_object* v_idx_764_){
_start:
{
lean_object* v___x_765_; 
v___x_765_ = l_Lean_Meta_Sym_Internal_mkBVarS___redArg(v_inst_763_, v_idx_764_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS___redArg(lean_object* v_inst_766_, lean_object* v_u_767_){
_start:
{
lean_object* v_share1_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v_share1_768_ = lean_ctor_get(v_inst_766_, 0);
lean_inc(v_share1_768_);
lean_dec_ref(v_inst_766_);
v___x_769_ = l_Lean_Expr_sort___override(v_u_767_);
v___x_770_ = lean_apply_1(v_share1_768_, v___x_769_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS(lean_object* v_m_771_, lean_object* v_inst_772_, lean_object* v_u_773_){
_start:
{
lean_object* v___x_774_; 
v___x_774_ = l_Lean_Meta_Sym_Internal_mkSortS___redArg(v_inst_772_, v_u_773_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___redArg(lean_object* v_inst_775_, lean_object* v_fvarId_776_){
_start:
{
lean_object* v_share1_777_; lean_object* v___x_778_; lean_object* v___x_779_; 
v_share1_777_ = lean_ctor_get(v_inst_775_, 0);
lean_inc(v_share1_777_);
lean_dec_ref(v_inst_775_);
v___x_778_ = l_Lean_Expr_fvar___override(v_fvarId_776_);
v___x_779_ = lean_apply_1(v_share1_777_, v___x_778_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS(lean_object* v_m_780_, lean_object* v_inst_781_, lean_object* v_fvarId_782_){
_start:
{
lean_object* v___x_783_; 
v___x_783_ = l_Lean_Meta_Sym_Internal_mkFVarS___redArg(v_inst_781_, v_fvarId_782_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMVarS___redArg(lean_object* v_inst_784_, lean_object* v_mvarId_785_){
_start:
{
lean_object* v_share1_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
v_share1_786_ = lean_ctor_get(v_inst_784_, 0);
lean_inc(v_share1_786_);
lean_dec_ref(v_inst_784_);
v___x_787_ = l_Lean_Expr_mvar___override(v_mvarId_785_);
v___x_788_ = lean_apply_1(v_share1_786_, v___x_787_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMVarS(lean_object* v_m_789_, lean_object* v_inst_790_, lean_object* v_mvarId_791_){
_start:
{
lean_object* v___x_792_; 
v___x_792_ = l_Lean_Meta_Sym_Internal_mkMVarS___redArg(v_inst_790_, v_mvarId_791_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__0(lean_object* v_d_793_, lean_object* v_e_794_, lean_object* v_share1_795_, lean_object* v_____r_796_){
_start:
{
lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_797_ = l_Lean_Expr_mdata___override(v_d_793_, v_e_794_);
v___x_798_ = lean_apply_1(v_share1_795_, v___x_797_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1(lean_object* v___f_799_, lean_object* v_____r_800_){
_start:
{
lean_object* v___x_801_; 
v___x_801_ = lean_apply_1(v___f_799_, v_____r_800_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__2(lean_object* v___f_802_, lean_object* v_assertShared_803_, lean_object* v_e_804_, lean_object* v_toBind_805_, lean_object* v___f_806_, uint8_t v_____do__lift_807_){
_start:
{
if (v_____do__lift_807_ == 0)
{
lean_object* v___x_808_; lean_object* v___x_809_; 
lean_dec(v___f_806_);
lean_dec(v_toBind_805_);
lean_dec_ref(v_e_804_);
lean_dec(v_assertShared_803_);
v___x_808_ = lean_box(0);
v___x_809_ = lean_apply_1(v___f_802_, v___x_808_);
return v___x_809_;
}
else
{
lean_object* v___x_810_; lean_object* v___x_811_; 
lean_dec(v___f_802_);
v___x_810_ = lean_apply_1(v_assertShared_803_, v_e_804_);
v___x_811_ = lean_apply_4(v_toBind_805_, lean_box(0), lean_box(0), v___x_810_, v___f_806_);
return v___x_811_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__2___boxed(lean_object* v___f_812_, lean_object* v_assertShared_813_, lean_object* v_e_814_, lean_object* v_toBind_815_, lean_object* v___f_816_, lean_object* v_____do__lift_817_){
_start:
{
uint8_t v_____do__lift_86__boxed_818_; lean_object* v_res_819_; 
v_____do__lift_86__boxed_818_ = lean_unbox(v_____do__lift_817_);
v_res_819_ = l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__2(v___f_812_, v_assertShared_813_, v_e_814_, v_toBind_815_, v___f_816_, v_____do__lift_86__boxed_818_);
return v_res_819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg(lean_object* v_inst_820_, lean_object* v_inst_821_, lean_object* v_d_822_, lean_object* v_e_823_){
_start:
{
lean_object* v_toBind_824_; lean_object* v_share1_825_; lean_object* v_assertShared_826_; lean_object* v_isDebugEnabled_827_; lean_object* v___f_828_; lean_object* v___f_829_; lean_object* v___f_830_; lean_object* v___x_831_; 
v_toBind_824_ = lean_ctor_get(v_inst_821_, 1);
lean_inc_n(v_toBind_824_, 2);
lean_dec_ref(v_inst_821_);
v_share1_825_ = lean_ctor_get(v_inst_820_, 0);
lean_inc(v_share1_825_);
v_assertShared_826_ = lean_ctor_get(v_inst_820_, 1);
lean_inc(v_assertShared_826_);
v_isDebugEnabled_827_ = lean_ctor_get(v_inst_820_, 2);
lean_inc(v_isDebugEnabled_827_);
lean_dec_ref(v_inst_820_);
lean_inc_ref(v_e_823_);
v___f_828_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__0), 4, 3);
lean_closure_set(v___f_828_, 0, v_d_822_);
lean_closure_set(v___f_828_, 1, v_e_823_);
lean_closure_set(v___f_828_, 2, v_share1_825_);
lean_inc_ref(v___f_828_);
v___f_829_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_829_, 0, v___f_828_);
v___f_830_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_830_, 0, v___f_828_);
lean_closure_set(v___f_830_, 1, v_assertShared_826_);
lean_closure_set(v___f_830_, 2, v_e_823_);
lean_closure_set(v___f_830_, 3, v_toBind_824_);
lean_closure_set(v___f_830_, 4, v___f_829_);
v___x_831_ = lean_apply_4(v_toBind_824_, lean_box(0), lean_box(0), v_isDebugEnabled_827_, v___f_830_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS(lean_object* v_m_832_, lean_object* v_inst_833_, lean_object* v_inst_834_, lean_object* v_d_835_, lean_object* v_e_836_){
_start:
{
lean_object* v___x_837_; 
v___x_837_ = l_Lean_Meta_Sym_Internal_mkMDataS___redArg(v_inst_833_, v_inst_834_, v_d_835_, v_e_836_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__0(lean_object* v_structName_838_, lean_object* v_idx_839_, lean_object* v_struct_840_, lean_object* v_share1_841_, lean_object* v_____r_842_){
_start:
{
lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_843_ = l_Lean_Expr_proj___override(v_structName_838_, v_idx_839_, v_struct_840_);
v___x_844_ = lean_apply_1(v_share1_841_, v___x_843_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__2(lean_object* v___f_845_, lean_object* v_assertShared_846_, lean_object* v_struct_847_, lean_object* v_toBind_848_, lean_object* v___f_849_, uint8_t v_____do__lift_850_){
_start:
{
if (v_____do__lift_850_ == 0)
{
lean_object* v___x_851_; lean_object* v___x_852_; 
lean_dec(v___f_849_);
lean_dec(v_toBind_848_);
lean_dec_ref(v_struct_847_);
lean_dec(v_assertShared_846_);
v___x_851_ = lean_box(0);
v___x_852_ = lean_apply_1(v___f_845_, v___x_851_);
return v___x_852_;
}
else
{
lean_object* v___x_853_; lean_object* v___x_854_; 
lean_dec(v___f_845_);
v___x_853_ = lean_apply_1(v_assertShared_846_, v_struct_847_);
v___x_854_ = lean_apply_4(v_toBind_848_, lean_box(0), lean_box(0), v___x_853_, v___f_849_);
return v___x_854_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__2___boxed(lean_object* v___f_855_, lean_object* v_assertShared_856_, lean_object* v_struct_857_, lean_object* v_toBind_858_, lean_object* v___f_859_, lean_object* v_____do__lift_860_){
_start:
{
uint8_t v_____do__lift_80__boxed_861_; lean_object* v_res_862_; 
v_____do__lift_80__boxed_861_ = lean_unbox(v_____do__lift_860_);
v_res_862_ = l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__2(v___f_855_, v_assertShared_856_, v_struct_857_, v_toBind_858_, v___f_859_, v_____do__lift_80__boxed_861_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___redArg(lean_object* v_inst_863_, lean_object* v_inst_864_, lean_object* v_structName_865_, lean_object* v_idx_866_, lean_object* v_struct_867_){
_start:
{
lean_object* v_toBind_868_; lean_object* v_share1_869_; lean_object* v_assertShared_870_; lean_object* v_isDebugEnabled_871_; lean_object* v___f_872_; lean_object* v___f_873_; lean_object* v___f_874_; lean_object* v___x_875_; 
v_toBind_868_ = lean_ctor_get(v_inst_864_, 1);
lean_inc_n(v_toBind_868_, 2);
lean_dec_ref(v_inst_864_);
v_share1_869_ = lean_ctor_get(v_inst_863_, 0);
lean_inc(v_share1_869_);
v_assertShared_870_ = lean_ctor_get(v_inst_863_, 1);
lean_inc(v_assertShared_870_);
v_isDebugEnabled_871_ = lean_ctor_get(v_inst_863_, 2);
lean_inc(v_isDebugEnabled_871_);
lean_dec_ref(v_inst_863_);
lean_inc_ref(v_struct_867_);
v___f_872_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__0), 5, 4);
lean_closure_set(v___f_872_, 0, v_structName_865_);
lean_closure_set(v___f_872_, 1, v_idx_866_);
lean_closure_set(v___f_872_, 2, v_struct_867_);
lean_closure_set(v___f_872_, 3, v_share1_869_);
lean_inc_ref(v___f_872_);
v___f_873_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_873_, 0, v___f_872_);
v___f_874_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_874_, 0, v___f_872_);
lean_closure_set(v___f_874_, 1, v_assertShared_870_);
lean_closure_set(v___f_874_, 2, v_struct_867_);
lean_closure_set(v___f_874_, 3, v_toBind_868_);
lean_closure_set(v___f_874_, 4, v___f_873_);
v___x_875_ = lean_apply_4(v_toBind_868_, lean_box(0), lean_box(0), v_isDebugEnabled_871_, v___f_874_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS(lean_object* v_m_876_, lean_object* v_inst_877_, lean_object* v_inst_878_, lean_object* v_structName_879_, lean_object* v_idx_880_, lean_object* v_struct_881_){
_start:
{
lean_object* v___x_882_; 
v___x_882_ = l_Lean_Meta_Sym_Internal_mkProjS___redArg(v_inst_877_, v_inst_878_, v_structName_879_, v_idx_880_, v_struct_881_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__0(lean_object* v_f_883_, lean_object* v_a_884_, lean_object* v_share1_885_, lean_object* v_____r_886_){
_start:
{
lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_887_ = l_Lean_Expr_app___override(v_f_883_, v_a_884_);
v___x_888_ = lean_apply_1(v_share1_885_, v___x_887_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__2(lean_object* v_assertShared_889_, lean_object* v_a_890_, lean_object* v_toBind_891_, lean_object* v___f_892_, lean_object* v_____r_893_){
_start:
{
lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_894_ = lean_apply_1(v_assertShared_889_, v_a_890_);
v___x_895_ = lean_apply_4(v_toBind_891_, lean_box(0), lean_box(0), v___x_894_, v___f_892_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__1(lean_object* v___f_896_, lean_object* v_assertShared_897_, lean_object* v_a_898_, lean_object* v_toBind_899_, lean_object* v___f_900_, lean_object* v_f_901_, uint8_t v_____do__lift_902_){
_start:
{
if (v_____do__lift_902_ == 0)
{
lean_object* v___x_903_; lean_object* v___x_904_; 
lean_dec_ref(v_f_901_);
lean_dec(v___f_900_);
lean_dec(v_toBind_899_);
lean_dec_ref(v_a_898_);
lean_dec(v_assertShared_897_);
v___x_903_ = lean_box(0);
v___x_904_ = lean_apply_1(v___f_896_, v___x_903_);
return v___x_904_;
}
else
{
lean_object* v___f_905_; lean_object* v___x_906_; lean_object* v___x_907_; 
lean_dec(v___f_896_);
lean_inc(v_toBind_899_);
lean_inc(v_assertShared_897_);
v___f_905_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__2), 5, 4);
lean_closure_set(v___f_905_, 0, v_assertShared_897_);
lean_closure_set(v___f_905_, 1, v_a_898_);
lean_closure_set(v___f_905_, 2, v_toBind_899_);
lean_closure_set(v___f_905_, 3, v___f_900_);
v___x_906_ = lean_apply_1(v_assertShared_897_, v_f_901_);
v___x_907_ = lean_apply_4(v_toBind_899_, lean_box(0), lean_box(0), v___x_906_, v___f_905_);
return v___x_907_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__1___boxed(lean_object* v___f_908_, lean_object* v_assertShared_909_, lean_object* v_a_910_, lean_object* v_toBind_911_, lean_object* v___f_912_, lean_object* v_f_913_, lean_object* v_____do__lift_914_){
_start:
{
uint8_t v_____do__lift_105__boxed_915_; lean_object* v_res_916_; 
v_____do__lift_105__boxed_915_ = lean_unbox(v_____do__lift_914_);
v_res_916_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__1(v___f_908_, v_assertShared_909_, v_a_910_, v_toBind_911_, v___f_912_, v_f_913_, v_____do__lift_105__boxed_915_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg(lean_object* v_inst_917_, lean_object* v_inst_918_, lean_object* v_f_919_, lean_object* v_a_920_){
_start:
{
lean_object* v_toBind_921_; lean_object* v_share1_922_; lean_object* v_assertShared_923_; lean_object* v_isDebugEnabled_924_; lean_object* v___f_925_; lean_object* v___f_926_; lean_object* v___f_927_; lean_object* v___x_928_; 
v_toBind_921_ = lean_ctor_get(v_inst_918_, 1);
lean_inc_n(v_toBind_921_, 2);
lean_dec_ref(v_inst_918_);
v_share1_922_ = lean_ctor_get(v_inst_917_, 0);
lean_inc(v_share1_922_);
v_assertShared_923_ = lean_ctor_get(v_inst_917_, 1);
lean_inc(v_assertShared_923_);
v_isDebugEnabled_924_ = lean_ctor_get(v_inst_917_, 2);
lean_inc(v_isDebugEnabled_924_);
lean_dec_ref(v_inst_917_);
lean_inc_ref(v_a_920_);
lean_inc_ref(v_f_919_);
v___f_925_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__0), 4, 3);
lean_closure_set(v___f_925_, 0, v_f_919_);
lean_closure_set(v___f_925_, 1, v_a_920_);
lean_closure_set(v___f_925_, 2, v_share1_922_);
lean_inc_ref(v___f_925_);
v___f_926_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_926_, 0, v___f_925_);
v___f_927_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_927_, 0, v___f_925_);
lean_closure_set(v___f_927_, 1, v_assertShared_923_);
lean_closure_set(v___f_927_, 2, v_a_920_);
lean_closure_set(v___f_927_, 3, v_toBind_921_);
lean_closure_set(v___f_927_, 4, v___f_926_);
lean_closure_set(v___f_927_, 5, v_f_919_);
v___x_928_ = lean_apply_4(v_toBind_921_, lean_box(0), lean_box(0), v_isDebugEnabled_924_, v___f_927_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS(lean_object* v_m_929_, lean_object* v_inst_930_, lean_object* v_inst_931_, lean_object* v_f_932_, lean_object* v_a_933_){
_start:
{
lean_object* v___x_934_; 
v___x_934_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_930_, v_inst_931_, v_f_932_, v_a_933_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__0(lean_object* v_x_935_, lean_object* v_t_936_, lean_object* v_b_937_, uint8_t v_bi_938_, lean_object* v_share1_939_, lean_object* v_____r_940_){
_start:
{
lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_941_ = l_Lean_Expr_lam___override(v_x_935_, v_t_936_, v_b_937_, v_bi_938_);
v___x_942_ = lean_apply_1(v_share1_939_, v___x_941_);
return v___x_942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__0___boxed(lean_object* v_x_943_, lean_object* v_t_944_, lean_object* v_b_945_, lean_object* v_bi_946_, lean_object* v_share1_947_, lean_object* v_____r_948_){
_start:
{
uint8_t v_bi_boxed_949_; lean_object* v_res_950_; 
v_bi_boxed_949_ = lean_unbox(v_bi_946_);
v_res_950_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__0(v_x_943_, v_t_944_, v_b_945_, v_bi_boxed_949_, v_share1_947_, v_____r_948_);
return v_res_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__2(lean_object* v_assertShared_951_, lean_object* v_b_952_, lean_object* v_toBind_953_, lean_object* v___f_954_, lean_object* v_____r_955_){
_start:
{
lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_956_ = lean_apply_1(v_assertShared_951_, v_b_952_);
v___x_957_ = lean_apply_4(v_toBind_953_, lean_box(0), lean_box(0), v___x_956_, v___f_954_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1(lean_object* v___f_958_, lean_object* v_assertShared_959_, lean_object* v_b_960_, lean_object* v_toBind_961_, lean_object* v___f_962_, lean_object* v_t_963_, uint8_t v_____do__lift_964_){
_start:
{
if (v_____do__lift_964_ == 0)
{
lean_object* v___x_965_; lean_object* v___x_966_; 
lean_dec_ref(v_t_963_);
lean_dec(v___f_962_);
lean_dec(v_toBind_961_);
lean_dec_ref(v_b_960_);
lean_dec(v_assertShared_959_);
v___x_965_ = lean_box(0);
v___x_966_ = lean_apply_1(v___f_958_, v___x_965_);
return v___x_966_;
}
else
{
lean_object* v___f_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
lean_dec(v___f_958_);
lean_inc(v_toBind_961_);
lean_inc(v_assertShared_959_);
v___f_967_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__2), 5, 4);
lean_closure_set(v___f_967_, 0, v_assertShared_959_);
lean_closure_set(v___f_967_, 1, v_b_960_);
lean_closure_set(v___f_967_, 2, v_toBind_961_);
lean_closure_set(v___f_967_, 3, v___f_962_);
v___x_968_ = lean_apply_1(v_assertShared_959_, v_t_963_);
v___x_969_ = lean_apply_4(v_toBind_961_, lean_box(0), lean_box(0), v___x_968_, v___f_967_);
return v___x_969_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1___boxed(lean_object* v___f_970_, lean_object* v_assertShared_971_, lean_object* v_b_972_, lean_object* v_toBind_973_, lean_object* v___f_974_, lean_object* v_t_975_, lean_object* v_____do__lift_976_){
_start:
{
uint8_t v_____do__lift_106__boxed_977_; lean_object* v_res_978_; 
v_____do__lift_106__boxed_977_ = lean_unbox(v_____do__lift_976_);
v_res_978_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1(v___f_970_, v_assertShared_971_, v_b_972_, v_toBind_973_, v___f_974_, v_t_975_, v_____do__lift_106__boxed_977_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(lean_object* v_inst_979_, lean_object* v_inst_980_, lean_object* v_x_981_, uint8_t v_bi_982_, lean_object* v_t_983_, lean_object* v_b_984_){
_start:
{
lean_object* v_toBind_985_; lean_object* v_share1_986_; lean_object* v_assertShared_987_; lean_object* v_isDebugEnabled_988_; lean_object* v___x_989_; lean_object* v___f_990_; lean_object* v___f_991_; lean_object* v___f_992_; lean_object* v___x_993_; 
v_toBind_985_ = lean_ctor_get(v_inst_980_, 1);
lean_inc_n(v_toBind_985_, 2);
lean_dec_ref(v_inst_980_);
v_share1_986_ = lean_ctor_get(v_inst_979_, 0);
lean_inc(v_share1_986_);
v_assertShared_987_ = lean_ctor_get(v_inst_979_, 1);
lean_inc(v_assertShared_987_);
v_isDebugEnabled_988_ = lean_ctor_get(v_inst_979_, 2);
lean_inc(v_isDebugEnabled_988_);
lean_dec_ref(v_inst_979_);
v___x_989_ = lean_box(v_bi_982_);
lean_inc_ref(v_b_984_);
lean_inc_ref(v_t_983_);
v___f_990_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_990_, 0, v_x_981_);
lean_closure_set(v___f_990_, 1, v_t_983_);
lean_closure_set(v___f_990_, 2, v_b_984_);
lean_closure_set(v___f_990_, 3, v___x_989_);
lean_closure_set(v___f_990_, 4, v_share1_986_);
lean_inc_ref(v___f_990_);
v___f_991_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_991_, 0, v___f_990_);
v___f_992_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_992_, 0, v___f_990_);
lean_closure_set(v___f_992_, 1, v_assertShared_987_);
lean_closure_set(v___f_992_, 2, v_b_984_);
lean_closure_set(v___f_992_, 3, v_toBind_985_);
lean_closure_set(v___f_992_, 4, v___f_991_);
lean_closure_set(v___f_992_, 5, v_t_983_);
v___x_993_ = lean_apply_4(v_toBind_985_, lean_box(0), lean_box(0), v_isDebugEnabled_988_, v___f_992_);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___boxed(lean_object* v_inst_994_, lean_object* v_inst_995_, lean_object* v_x_996_, lean_object* v_bi_997_, lean_object* v_t_998_, lean_object* v_b_999_){
_start:
{
uint8_t v_bi_boxed_1000_; lean_object* v_res_1001_; 
v_bi_boxed_1000_ = lean_unbox(v_bi_997_);
v_res_1001_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v_inst_994_, v_inst_995_, v_x_996_, v_bi_boxed_1000_, v_t_998_, v_b_999_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS(lean_object* v_m_1002_, lean_object* v_inst_1003_, lean_object* v_inst_1004_, lean_object* v_x_1005_, uint8_t v_bi_1006_, lean_object* v_t_1007_, lean_object* v_b_1008_){
_start:
{
lean_object* v___x_1009_; 
v___x_1009_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v_inst_1003_, v_inst_1004_, v_x_1005_, v_bi_1006_, v_t_1007_, v_b_1008_);
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___boxed(lean_object* v_m_1010_, lean_object* v_inst_1011_, lean_object* v_inst_1012_, lean_object* v_x_1013_, lean_object* v_bi_1014_, lean_object* v_t_1015_, lean_object* v_b_1016_){
_start:
{
uint8_t v_bi_boxed_1017_; lean_object* v_res_1018_; 
v_bi_boxed_1017_ = lean_unbox(v_bi_1014_);
v_res_1018_ = l_Lean_Meta_Sym_Internal_mkLambdaS(v_m_1010_, v_inst_1011_, v_inst_1012_, v_x_1013_, v_bi_boxed_1017_, v_t_1015_, v_b_1016_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___redArg___lam__0(lean_object* v_x_1019_, lean_object* v_t_1020_, lean_object* v_b_1021_, uint8_t v_bi_1022_, lean_object* v_share1_1023_, lean_object* v_____r_1024_){
_start:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1025_ = l_Lean_Expr_forallE___override(v_x_1019_, v_t_1020_, v_b_1021_, v_bi_1022_);
v___x_1026_ = lean_apply_1(v_share1_1023_, v___x_1025_);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___redArg___lam__0___boxed(lean_object* v_x_1027_, lean_object* v_t_1028_, lean_object* v_b_1029_, lean_object* v_bi_1030_, lean_object* v_share1_1031_, lean_object* v_____r_1032_){
_start:
{
uint8_t v_bi_boxed_1033_; lean_object* v_res_1034_; 
v_bi_boxed_1033_ = lean_unbox(v_bi_1030_);
v_res_1034_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg___lam__0(v_x_1027_, v_t_1028_, v_b_1029_, v_bi_boxed_1033_, v_share1_1031_, v_____r_1032_);
return v_res_1034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___redArg(lean_object* v_inst_1035_, lean_object* v_inst_1036_, lean_object* v_x_1037_, uint8_t v_bi_1038_, lean_object* v_t_1039_, lean_object* v_b_1040_){
_start:
{
lean_object* v_toBind_1041_; lean_object* v_share1_1042_; lean_object* v_assertShared_1043_; lean_object* v_isDebugEnabled_1044_; lean_object* v___x_1045_; lean_object* v___f_1046_; lean_object* v___f_1047_; lean_object* v___f_1048_; lean_object* v___x_1049_; 
v_toBind_1041_ = lean_ctor_get(v_inst_1036_, 1);
lean_inc_n(v_toBind_1041_, 2);
lean_dec_ref(v_inst_1036_);
v_share1_1042_ = lean_ctor_get(v_inst_1035_, 0);
lean_inc(v_share1_1042_);
v_assertShared_1043_ = lean_ctor_get(v_inst_1035_, 1);
lean_inc(v_assertShared_1043_);
v_isDebugEnabled_1044_ = lean_ctor_get(v_inst_1035_, 2);
lean_inc(v_isDebugEnabled_1044_);
lean_dec_ref(v_inst_1035_);
v___x_1045_ = lean_box(v_bi_1038_);
lean_inc_ref(v_b_1040_);
lean_inc_ref(v_t_1039_);
v___f_1046_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkForallS___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1046_, 0, v_x_1037_);
lean_closure_set(v___f_1046_, 1, v_t_1039_);
lean_closure_set(v___f_1046_, 2, v_b_1040_);
lean_closure_set(v___f_1046_, 3, v___x_1045_);
lean_closure_set(v___f_1046_, 4, v_share1_1042_);
lean_inc_ref(v___f_1046_);
v___f_1047_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1047_, 0, v___f_1046_);
v___f_1048_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_1048_, 0, v___f_1046_);
lean_closure_set(v___f_1048_, 1, v_assertShared_1043_);
lean_closure_set(v___f_1048_, 2, v_b_1040_);
lean_closure_set(v___f_1048_, 3, v_toBind_1041_);
lean_closure_set(v___f_1048_, 4, v___f_1047_);
lean_closure_set(v___f_1048_, 5, v_t_1039_);
v___x_1049_ = lean_apply_4(v_toBind_1041_, lean_box(0), lean_box(0), v_isDebugEnabled_1044_, v___f_1048_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___redArg___boxed(lean_object* v_inst_1050_, lean_object* v_inst_1051_, lean_object* v_x_1052_, lean_object* v_bi_1053_, lean_object* v_t_1054_, lean_object* v_b_1055_){
_start:
{
uint8_t v_bi_boxed_1056_; lean_object* v_res_1057_; 
v_bi_boxed_1056_ = lean_unbox(v_bi_1053_);
v_res_1057_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v_inst_1050_, v_inst_1051_, v_x_1052_, v_bi_boxed_1056_, v_t_1054_, v_b_1055_);
return v_res_1057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS(lean_object* v_m_1058_, lean_object* v_inst_1059_, lean_object* v_inst_1060_, lean_object* v_x_1061_, uint8_t v_bi_1062_, lean_object* v_t_1063_, lean_object* v_b_1064_){
_start:
{
lean_object* v___x_1065_; 
v___x_1065_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v_inst_1059_, v_inst_1060_, v_x_1061_, v_bi_1062_, v_t_1063_, v_b_1064_);
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___boxed(lean_object* v_m_1066_, lean_object* v_inst_1067_, lean_object* v_inst_1068_, lean_object* v_x_1069_, lean_object* v_bi_1070_, lean_object* v_t_1071_, lean_object* v_b_1072_){
_start:
{
uint8_t v_bi_boxed_1073_; lean_object* v_res_1074_; 
v_bi_boxed_1073_ = lean_unbox(v_bi_1070_);
v_res_1074_ = l_Lean_Meta_Sym_Internal_mkForallS(v_m_1066_, v_inst_1067_, v_inst_1068_, v_x_1069_, v_bi_boxed_1073_, v_t_1071_, v_b_1072_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__0(lean_object* v_x_1075_, lean_object* v_t_1076_, lean_object* v_v_1077_, lean_object* v_b_1078_, uint8_t v_nondep_1079_, lean_object* v_share1_1080_, lean_object* v_____r_1081_){
_start:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1082_ = l_Lean_Expr_letE___override(v_x_1075_, v_t_1076_, v_v_1077_, v_b_1078_, v_nondep_1079_);
v___x_1083_ = lean_apply_1(v_share1_1080_, v___x_1082_);
return v___x_1083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__0___boxed(lean_object* v_x_1084_, lean_object* v_t_1085_, lean_object* v_v_1086_, lean_object* v_b_1087_, lean_object* v_nondep_1088_, lean_object* v_share1_1089_, lean_object* v_____r_1090_){
_start:
{
uint8_t v_nondep_boxed_1091_; lean_object* v_res_1092_; 
v_nondep_boxed_1091_ = lean_unbox(v_nondep_1088_);
v_res_1092_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__0(v_x_1084_, v_t_1085_, v_v_1086_, v_b_1087_, v_nondep_boxed_1091_, v_share1_1089_, v_____r_1090_);
return v_res_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__3(lean_object* v_assertShared_1093_, lean_object* v_v_1094_, lean_object* v_toBind_1095_, lean_object* v___f_1096_, lean_object* v_____r_1097_){
_start:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1098_ = lean_apply_1(v_assertShared_1093_, v_v_1094_);
v___x_1099_ = lean_apply_4(v_toBind_1095_, lean_box(0), lean_box(0), v___x_1098_, v___f_1096_);
return v___x_1099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1(lean_object* v___f_1100_, lean_object* v_assertShared_1101_, lean_object* v_b_1102_, lean_object* v_toBind_1103_, lean_object* v___f_1104_, lean_object* v_v_1105_, lean_object* v_t_1106_, uint8_t v_____do__lift_1107_){
_start:
{
if (v_____do__lift_1107_ == 0)
{
lean_object* v___x_1108_; lean_object* v___x_1109_; 
lean_dec_ref(v_t_1106_);
lean_dec_ref(v_v_1105_);
lean_dec(v___f_1104_);
lean_dec(v_toBind_1103_);
lean_dec_ref(v_b_1102_);
lean_dec(v_assertShared_1101_);
v___x_1108_ = lean_box(0);
v___x_1109_ = lean_apply_1(v___f_1100_, v___x_1108_);
return v___x_1109_;
}
else
{
lean_object* v___f_1110_; lean_object* v___f_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; 
lean_dec(v___f_1100_);
lean_inc_n(v_toBind_1103_, 2);
lean_inc_n(v_assertShared_1101_, 2);
v___f_1110_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__2), 5, 4);
lean_closure_set(v___f_1110_, 0, v_assertShared_1101_);
lean_closure_set(v___f_1110_, 1, v_b_1102_);
lean_closure_set(v___f_1110_, 2, v_toBind_1103_);
lean_closure_set(v___f_1110_, 3, v___f_1104_);
v___f_1111_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__3), 5, 4);
lean_closure_set(v___f_1111_, 0, v_assertShared_1101_);
lean_closure_set(v___f_1111_, 1, v_v_1105_);
lean_closure_set(v___f_1111_, 2, v_toBind_1103_);
lean_closure_set(v___f_1111_, 3, v___f_1110_);
v___x_1112_ = lean_apply_1(v_assertShared_1101_, v_t_1106_);
v___x_1113_ = lean_apply_4(v_toBind_1103_, lean_box(0), lean_box(0), v___x_1112_, v___f_1111_);
return v___x_1113_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1___boxed(lean_object* v___f_1114_, lean_object* v_assertShared_1115_, lean_object* v_b_1116_, lean_object* v_toBind_1117_, lean_object* v___f_1118_, lean_object* v_v_1119_, lean_object* v_t_1120_, lean_object* v_____do__lift_1121_){
_start:
{
uint8_t v_____do__lift_123__boxed_1122_; lean_object* v_res_1123_; 
v_____do__lift_123__boxed_1122_ = lean_unbox(v_____do__lift_1121_);
v_res_1123_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1(v___f_1114_, v_assertShared_1115_, v_b_1116_, v_toBind_1117_, v___f_1118_, v_v_1119_, v_t_1120_, v_____do__lift_123__boxed_1122_);
return v_res_1123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg(lean_object* v_inst_1124_, lean_object* v_inst_1125_, lean_object* v_x_1126_, lean_object* v_t_1127_, lean_object* v_v_1128_, lean_object* v_b_1129_, uint8_t v_nondep_1130_){
_start:
{
lean_object* v_toBind_1131_; lean_object* v_share1_1132_; lean_object* v_assertShared_1133_; lean_object* v_isDebugEnabled_1134_; lean_object* v___x_1135_; lean_object* v___f_1136_; lean_object* v___f_1137_; lean_object* v___f_1138_; lean_object* v___x_1139_; 
v_toBind_1131_ = lean_ctor_get(v_inst_1125_, 1);
lean_inc_n(v_toBind_1131_, 2);
lean_dec_ref(v_inst_1125_);
v_share1_1132_ = lean_ctor_get(v_inst_1124_, 0);
lean_inc(v_share1_1132_);
v_assertShared_1133_ = lean_ctor_get(v_inst_1124_, 1);
lean_inc(v_assertShared_1133_);
v_isDebugEnabled_1134_ = lean_ctor_get(v_inst_1124_, 2);
lean_inc(v_isDebugEnabled_1134_);
lean_dec_ref(v_inst_1124_);
v___x_1135_ = lean_box(v_nondep_1130_);
lean_inc_ref(v_b_1129_);
lean_inc_ref(v_v_1128_);
lean_inc_ref(v_t_1127_);
v___f_1136_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_1136_, 0, v_x_1126_);
lean_closure_set(v___f_1136_, 1, v_t_1127_);
lean_closure_set(v___f_1136_, 2, v_v_1128_);
lean_closure_set(v___f_1136_, 3, v_b_1129_);
lean_closure_set(v___f_1136_, 4, v___x_1135_);
lean_closure_set(v___f_1136_, 5, v_share1_1132_);
lean_inc_ref(v___f_1136_);
v___f_1137_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1137_, 0, v___f_1136_);
v___f_1138_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_1138_, 0, v___f_1136_);
lean_closure_set(v___f_1138_, 1, v_assertShared_1133_);
lean_closure_set(v___f_1138_, 2, v_b_1129_);
lean_closure_set(v___f_1138_, 3, v_toBind_1131_);
lean_closure_set(v___f_1138_, 4, v___f_1137_);
lean_closure_set(v___f_1138_, 5, v_v_1128_);
lean_closure_set(v___f_1138_, 6, v_t_1127_);
v___x_1139_ = lean_apply_4(v_toBind_1131_, lean_box(0), lean_box(0), v_isDebugEnabled_1134_, v___f_1138_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___boxed(lean_object* v_inst_1140_, lean_object* v_inst_1141_, lean_object* v_x_1142_, lean_object* v_t_1143_, lean_object* v_v_1144_, lean_object* v_b_1145_, lean_object* v_nondep_1146_){
_start:
{
uint8_t v_nondep_boxed_1147_; lean_object* v_res_1148_; 
v_nondep_boxed_1147_ = lean_unbox(v_nondep_1146_);
v_res_1148_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1140_, v_inst_1141_, v_x_1142_, v_t_1143_, v_v_1144_, v_b_1145_, v_nondep_boxed_1147_);
return v_res_1148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS(lean_object* v_m_1149_, lean_object* v_inst_1150_, lean_object* v_inst_1151_, lean_object* v_x_1152_, lean_object* v_t_1153_, lean_object* v_v_1154_, lean_object* v_b_1155_, uint8_t v_nondep_1156_){
_start:
{
lean_object* v___x_1157_; 
v___x_1157_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1150_, v_inst_1151_, v_x_1152_, v_t_1153_, v_v_1154_, v_b_1155_, v_nondep_1156_);
return v___x_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___boxed(lean_object* v_m_1158_, lean_object* v_inst_1159_, lean_object* v_inst_1160_, lean_object* v_x_1161_, lean_object* v_t_1162_, lean_object* v_v_1163_, lean_object* v_b_1164_, lean_object* v_nondep_1165_){
_start:
{
uint8_t v_nondep_boxed_1166_; lean_object* v_res_1167_; 
v_nondep_boxed_1166_ = lean_unbox(v_nondep_1165_);
v_res_1167_ = l_Lean_Meta_Sym_Internal_mkLetS(v_m_1158_, v_inst_1159_, v_inst_1160_, v_x_1161_, v_t_1162_, v_v_1163_, v_b_1164_, v_nondep_boxed_1166_);
return v_res_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkHaveS___redArg___lam__0(lean_object* v_x_1168_, lean_object* v_t_1169_, lean_object* v_v_1170_, lean_object* v_b_1171_, lean_object* v_share1_1172_, lean_object* v_____r_1173_){
_start:
{
uint8_t v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___x_1174_ = 1;
v___x_1175_ = l_Lean_Expr_letE___override(v_x_1168_, v_t_1169_, v_v_1170_, v_b_1171_, v___x_1174_);
v___x_1176_ = lean_apply_1(v_share1_1172_, v___x_1175_);
return v___x_1176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkHaveS___redArg(lean_object* v_inst_1177_, lean_object* v_inst_1178_, lean_object* v_x_1179_, lean_object* v_t_1180_, lean_object* v_v_1181_, lean_object* v_b_1182_){
_start:
{
lean_object* v_toBind_1183_; lean_object* v_share1_1184_; lean_object* v_assertShared_1185_; lean_object* v_isDebugEnabled_1186_; lean_object* v___f_1187_; lean_object* v___f_1188_; lean_object* v___f_1189_; lean_object* v___x_1190_; 
v_toBind_1183_ = lean_ctor_get(v_inst_1178_, 1);
lean_inc_n(v_toBind_1183_, 2);
lean_dec_ref(v_inst_1178_);
v_share1_1184_ = lean_ctor_get(v_inst_1177_, 0);
lean_inc(v_share1_1184_);
v_assertShared_1185_ = lean_ctor_get(v_inst_1177_, 1);
lean_inc(v_assertShared_1185_);
v_isDebugEnabled_1186_ = lean_ctor_get(v_inst_1177_, 2);
lean_inc(v_isDebugEnabled_1186_);
lean_dec_ref(v_inst_1177_);
lean_inc_ref(v_b_1182_);
lean_inc_ref(v_v_1181_);
lean_inc_ref(v_t_1180_);
v___f_1187_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkHaveS___redArg___lam__0), 6, 5);
lean_closure_set(v___f_1187_, 0, v_x_1179_);
lean_closure_set(v___f_1187_, 1, v_t_1180_);
lean_closure_set(v___f_1187_, 2, v_v_1181_);
lean_closure_set(v___f_1187_, 3, v_b_1182_);
lean_closure_set(v___f_1187_, 4, v_share1_1184_);
lean_inc_ref(v___f_1187_);
v___f_1188_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1188_, 0, v___f_1187_);
v___f_1189_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_1189_, 0, v___f_1187_);
lean_closure_set(v___f_1189_, 1, v_assertShared_1185_);
lean_closure_set(v___f_1189_, 2, v_b_1182_);
lean_closure_set(v___f_1189_, 3, v_toBind_1183_);
lean_closure_set(v___f_1189_, 4, v___f_1188_);
lean_closure_set(v___f_1189_, 5, v_v_1181_);
lean_closure_set(v___f_1189_, 6, v_t_1180_);
v___x_1190_ = lean_apply_4(v_toBind_1183_, lean_box(0), lean_box(0), v_isDebugEnabled_1186_, v___f_1189_);
return v___x_1190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkHaveS(lean_object* v_m_1191_, lean_object* v_inst_1192_, lean_object* v_inst_1193_, lean_object* v_x_1194_, lean_object* v_t_1195_, lean_object* v_v_1196_, lean_object* v_b_1197_){
_start:
{
lean_object* v___x_1198_; 
v___x_1198_ = l_Lean_Meta_Sym_Internal_mkHaveS___redArg(v_inst_1192_, v_inst_1193_, v_x_1194_, v_t_1195_, v_v_1196_, v_b_1197_);
return v___x_1198_;
}
}
static lean_object* _init_l_Lean_Expr_updateAppS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1201_ = ((lean_object*)(l_Lean_Expr_updateAppS_x21___redArg___closed__1));
v___x_1202_ = lean_unsigned_to_nat(25u);
v___x_1203_ = lean_unsigned_to_nat(148u);
v___x_1204_ = ((lean_object*)(l_Lean_Expr_updateAppS_x21___redArg___closed__0));
v___x_1205_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1206_ = l_mkPanicMessageWithDecl(v___x_1205_, v___x_1204_, v___x_1203_, v___x_1202_, v___x_1201_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateAppS_x21___redArg(lean_object* v_inst_1207_, lean_object* v_inst_1208_, lean_object* v_e_1209_, lean_object* v_newFn_1210_, lean_object* v_newArg_1211_){
_start:
{
uint8_t v___y_1213_; 
if (lean_obj_tag(v_e_1209_) == 5)
{
lean_object* v_fn_1218_; lean_object* v_arg_1219_; size_t v___x_1220_; size_t v___x_1221_; uint8_t v___x_1222_; 
v_fn_1218_ = lean_ctor_get(v_e_1209_, 0);
v_arg_1219_ = lean_ctor_get(v_e_1209_, 1);
v___x_1220_ = lean_ptr_addr(v_fn_1218_);
v___x_1221_ = lean_ptr_addr(v_newFn_1210_);
v___x_1222_ = lean_usize_dec_eq(v___x_1220_, v___x_1221_);
if (v___x_1222_ == 0)
{
v___y_1213_ = v___x_1222_;
goto v___jp_1212_;
}
else
{
size_t v___x_1223_; size_t v___x_1224_; uint8_t v___x_1225_; 
v___x_1223_ = lean_ptr_addr(v_arg_1219_);
v___x_1224_ = lean_ptr_addr(v_newArg_1211_);
v___x_1225_ = lean_usize_dec_eq(v___x_1223_, v___x_1224_);
v___y_1213_ = v___x_1225_;
goto v___jp_1212_;
}
}
else
{
lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
lean_dec_ref(v_newArg_1211_);
lean_dec_ref(v_newFn_1210_);
lean_dec_ref(v_e_1209_);
lean_dec_ref(v_inst_1207_);
v___x_1226_ = l_Lean_instInhabitedExpr;
v___x_1227_ = l_instInhabitedOfMonad___redArg(v_inst_1208_, v___x_1226_);
v___x_1228_ = lean_obj_once(&l_Lean_Expr_updateAppS_x21___redArg___closed__2, &l_Lean_Expr_updateAppS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateAppS_x21___redArg___closed__2);
v___x_1229_ = l_panic___redArg(v___x_1227_, v___x_1228_);
lean_dec(v___x_1227_);
return v___x_1229_;
}
v___jp_1212_:
{
if (v___y_1213_ == 0)
{
lean_object* v___x_1214_; 
lean_dec_ref(v_e_1209_);
v___x_1214_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1207_, v_inst_1208_, v_newFn_1210_, v_newArg_1211_);
return v___x_1214_;
}
else
{
lean_object* v_toApplicative_1215_; lean_object* v_toPure_1216_; lean_object* v___x_1217_; 
lean_dec_ref(v_newArg_1211_);
lean_dec_ref(v_newFn_1210_);
lean_dec_ref(v_inst_1207_);
v_toApplicative_1215_ = lean_ctor_get(v_inst_1208_, 0);
lean_inc_ref(v_toApplicative_1215_);
lean_dec_ref(v_inst_1208_);
v_toPure_1216_ = lean_ctor_get(v_toApplicative_1215_, 1);
lean_inc(v_toPure_1216_);
lean_dec_ref(v_toApplicative_1215_);
v___x_1217_ = lean_apply_2(v_toPure_1216_, lean_box(0), v_e_1209_);
return v___x_1217_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateAppS_x21(lean_object* v_m_1230_, lean_object* v_inst_1231_, lean_object* v_inst_1232_, lean_object* v_e_1233_, lean_object* v_newFn_1234_, lean_object* v_newArg_1235_){
_start:
{
uint8_t v___y_1237_; 
if (lean_obj_tag(v_e_1233_) == 5)
{
lean_object* v_fn_1242_; lean_object* v_arg_1243_; size_t v___x_1244_; size_t v___x_1245_; uint8_t v___x_1246_; 
v_fn_1242_ = lean_ctor_get(v_e_1233_, 0);
v_arg_1243_ = lean_ctor_get(v_e_1233_, 1);
v___x_1244_ = lean_ptr_addr(v_fn_1242_);
v___x_1245_ = lean_ptr_addr(v_newFn_1234_);
v___x_1246_ = lean_usize_dec_eq(v___x_1244_, v___x_1245_);
if (v___x_1246_ == 0)
{
v___y_1237_ = v___x_1246_;
goto v___jp_1236_;
}
else
{
size_t v___x_1247_; size_t v___x_1248_; uint8_t v___x_1249_; 
v___x_1247_ = lean_ptr_addr(v_arg_1243_);
v___x_1248_ = lean_ptr_addr(v_newArg_1235_);
v___x_1249_ = lean_usize_dec_eq(v___x_1247_, v___x_1248_);
v___y_1237_ = v___x_1249_;
goto v___jp_1236_;
}
}
else
{
lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; 
lean_dec_ref(v_newArg_1235_);
lean_dec_ref(v_newFn_1234_);
lean_dec_ref(v_e_1233_);
lean_dec_ref(v_inst_1231_);
v___x_1250_ = l_Lean_instInhabitedExpr;
v___x_1251_ = l_instInhabitedOfMonad___redArg(v_inst_1232_, v___x_1250_);
v___x_1252_ = lean_obj_once(&l_Lean_Expr_updateAppS_x21___redArg___closed__2, &l_Lean_Expr_updateAppS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateAppS_x21___redArg___closed__2);
v___x_1253_ = l_panic___redArg(v___x_1251_, v___x_1252_);
lean_dec(v___x_1251_);
return v___x_1253_;
}
v___jp_1236_:
{
if (v___y_1237_ == 0)
{
lean_object* v___x_1238_; 
lean_dec_ref(v_e_1233_);
v___x_1238_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1231_, v_inst_1232_, v_newFn_1234_, v_newArg_1235_);
return v___x_1238_;
}
else
{
lean_object* v_toApplicative_1239_; lean_object* v_toPure_1240_; lean_object* v___x_1241_; 
lean_dec_ref(v_newArg_1235_);
lean_dec_ref(v_newFn_1234_);
lean_dec_ref(v_inst_1231_);
v_toApplicative_1239_ = lean_ctor_get(v_inst_1232_, 0);
lean_inc_ref(v_toApplicative_1239_);
lean_dec_ref(v_inst_1232_);
v_toPure_1240_ = lean_ctor_get(v_toApplicative_1239_, 1);
lean_inc(v_toPure_1240_);
lean_dec_ref(v_toApplicative_1239_);
v___x_1241_ = lean_apply_2(v_toPure_1240_, lean_box(0), v_e_1233_);
return v___x_1241_;
}
}
}
}
static lean_object* _init_l_Lean_Expr_updateMDataS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1256_ = ((lean_object*)(l_Lean_Expr_updateMDataS_x21___redArg___closed__1));
v___x_1257_ = lean_unsigned_to_nat(24u);
v___x_1258_ = lean_unsigned_to_nat(152u);
v___x_1259_ = ((lean_object*)(l_Lean_Expr_updateMDataS_x21___redArg___closed__0));
v___x_1260_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1261_ = l_mkPanicMessageWithDecl(v___x_1260_, v___x_1259_, v___x_1258_, v___x_1257_, v___x_1256_);
return v___x_1261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateMDataS_x21___redArg(lean_object* v_inst_1262_, lean_object* v_inst_1263_, lean_object* v_e_1264_, lean_object* v_newExpr_1265_){
_start:
{
if (lean_obj_tag(v_e_1264_) == 10)
{
lean_object* v_data_1266_; lean_object* v_expr_1267_; size_t v___x_1268_; size_t v___x_1269_; uint8_t v___x_1270_; 
v_data_1266_ = lean_ctor_get(v_e_1264_, 0);
v_expr_1267_ = lean_ctor_get(v_e_1264_, 1);
v___x_1268_ = lean_ptr_addr(v_expr_1267_);
v___x_1269_ = lean_ptr_addr(v_newExpr_1265_);
v___x_1270_ = lean_usize_dec_eq(v___x_1268_, v___x_1269_);
if (v___x_1270_ == 0)
{
lean_object* v___x_1271_; 
lean_inc(v_data_1266_);
lean_dec_ref_known(v_e_1264_, 2);
v___x_1271_ = l_Lean_Meta_Sym_Internal_mkMDataS___redArg(v_inst_1262_, v_inst_1263_, v_data_1266_, v_newExpr_1265_);
return v___x_1271_;
}
else
{
lean_object* v_toApplicative_1272_; lean_object* v_toPure_1273_; lean_object* v___x_1274_; 
lean_dec_ref(v_newExpr_1265_);
lean_dec_ref(v_inst_1262_);
v_toApplicative_1272_ = lean_ctor_get(v_inst_1263_, 0);
lean_inc_ref(v_toApplicative_1272_);
lean_dec_ref(v_inst_1263_);
v_toPure_1273_ = lean_ctor_get(v_toApplicative_1272_, 1);
lean_inc(v_toPure_1273_);
lean_dec_ref(v_toApplicative_1272_);
v___x_1274_ = lean_apply_2(v_toPure_1273_, lean_box(0), v_e_1264_);
return v___x_1274_;
}
}
else
{
lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; 
lean_dec_ref(v_newExpr_1265_);
lean_dec_ref(v_e_1264_);
lean_dec_ref(v_inst_1262_);
v___x_1275_ = l_Lean_instInhabitedExpr;
v___x_1276_ = l_instInhabitedOfMonad___redArg(v_inst_1263_, v___x_1275_);
v___x_1277_ = lean_obj_once(&l_Lean_Expr_updateMDataS_x21___redArg___closed__2, &l_Lean_Expr_updateMDataS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateMDataS_x21___redArg___closed__2);
v___x_1278_ = l_panic___redArg(v___x_1276_, v___x_1277_);
lean_dec(v___x_1276_);
return v___x_1278_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateMDataS_x21(lean_object* v_m_1279_, lean_object* v_inst_1280_, lean_object* v_inst_1281_, lean_object* v_e_1282_, lean_object* v_newExpr_1283_){
_start:
{
if (lean_obj_tag(v_e_1282_) == 10)
{
lean_object* v_data_1284_; lean_object* v_expr_1285_; size_t v___x_1286_; size_t v___x_1287_; uint8_t v___x_1288_; 
v_data_1284_ = lean_ctor_get(v_e_1282_, 0);
v_expr_1285_ = lean_ctor_get(v_e_1282_, 1);
v___x_1286_ = lean_ptr_addr(v_expr_1285_);
v___x_1287_ = lean_ptr_addr(v_newExpr_1283_);
v___x_1288_ = lean_usize_dec_eq(v___x_1286_, v___x_1287_);
if (v___x_1288_ == 0)
{
lean_object* v___x_1289_; 
lean_inc(v_data_1284_);
lean_dec_ref_known(v_e_1282_, 2);
v___x_1289_ = l_Lean_Meta_Sym_Internal_mkMDataS___redArg(v_inst_1280_, v_inst_1281_, v_data_1284_, v_newExpr_1283_);
return v___x_1289_;
}
else
{
lean_object* v_toApplicative_1290_; lean_object* v_toPure_1291_; lean_object* v___x_1292_; 
lean_dec_ref(v_newExpr_1283_);
lean_dec_ref(v_inst_1280_);
v_toApplicative_1290_ = lean_ctor_get(v_inst_1281_, 0);
lean_inc_ref(v_toApplicative_1290_);
lean_dec_ref(v_inst_1281_);
v_toPure_1291_ = lean_ctor_get(v_toApplicative_1290_, 1);
lean_inc(v_toPure_1291_);
lean_dec_ref(v_toApplicative_1290_);
v___x_1292_ = lean_apply_2(v_toPure_1291_, lean_box(0), v_e_1282_);
return v___x_1292_;
}
}
else
{
lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; 
lean_dec_ref(v_newExpr_1283_);
lean_dec_ref(v_e_1282_);
lean_dec_ref(v_inst_1280_);
v___x_1293_ = l_Lean_instInhabitedExpr;
v___x_1294_ = l_instInhabitedOfMonad___redArg(v_inst_1281_, v___x_1293_);
v___x_1295_ = lean_obj_once(&l_Lean_Expr_updateMDataS_x21___redArg___closed__2, &l_Lean_Expr_updateMDataS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateMDataS_x21___redArg___closed__2);
v___x_1296_ = l_panic___redArg(v___x_1294_, v___x_1295_);
lean_dec(v___x_1294_);
return v___x_1296_;
}
}
}
static lean_object* _init_l_Lean_Expr_updateProjS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; 
v___x_1299_ = ((lean_object*)(l_Lean_Expr_updateProjS_x21___redArg___closed__1));
v___x_1300_ = lean_unsigned_to_nat(25u);
v___x_1301_ = lean_unsigned_to_nat(156u);
v___x_1302_ = ((lean_object*)(l_Lean_Expr_updateProjS_x21___redArg___closed__0));
v___x_1303_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1304_ = l_mkPanicMessageWithDecl(v___x_1303_, v___x_1302_, v___x_1301_, v___x_1300_, v___x_1299_);
return v___x_1304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateProjS_x21___redArg(lean_object* v_inst_1305_, lean_object* v_inst_1306_, lean_object* v_e_1307_, lean_object* v_newExpr_1308_){
_start:
{
if (lean_obj_tag(v_e_1307_) == 11)
{
lean_object* v_typeName_1309_; lean_object* v_idx_1310_; lean_object* v_struct_1311_; size_t v___x_1312_; size_t v___x_1313_; uint8_t v___x_1314_; 
v_typeName_1309_ = lean_ctor_get(v_e_1307_, 0);
v_idx_1310_ = lean_ctor_get(v_e_1307_, 1);
v_struct_1311_ = lean_ctor_get(v_e_1307_, 2);
v___x_1312_ = lean_ptr_addr(v_struct_1311_);
v___x_1313_ = lean_ptr_addr(v_newExpr_1308_);
v___x_1314_ = lean_usize_dec_eq(v___x_1312_, v___x_1313_);
if (v___x_1314_ == 0)
{
lean_object* v___x_1315_; 
lean_inc(v_idx_1310_);
lean_inc(v_typeName_1309_);
lean_dec_ref_known(v_e_1307_, 3);
v___x_1315_ = l_Lean_Meta_Sym_Internal_mkProjS___redArg(v_inst_1305_, v_inst_1306_, v_typeName_1309_, v_idx_1310_, v_newExpr_1308_);
return v___x_1315_;
}
else
{
lean_object* v_toApplicative_1316_; lean_object* v_toPure_1317_; lean_object* v___x_1318_; 
lean_dec_ref(v_newExpr_1308_);
lean_dec_ref(v_inst_1305_);
v_toApplicative_1316_ = lean_ctor_get(v_inst_1306_, 0);
lean_inc_ref(v_toApplicative_1316_);
lean_dec_ref(v_inst_1306_);
v_toPure_1317_ = lean_ctor_get(v_toApplicative_1316_, 1);
lean_inc(v_toPure_1317_);
lean_dec_ref(v_toApplicative_1316_);
v___x_1318_ = lean_apply_2(v_toPure_1317_, lean_box(0), v_e_1307_);
return v___x_1318_;
}
}
else
{
lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; 
lean_dec_ref(v_newExpr_1308_);
lean_dec_ref(v_e_1307_);
lean_dec_ref(v_inst_1305_);
v___x_1319_ = l_Lean_instInhabitedExpr;
v___x_1320_ = l_instInhabitedOfMonad___redArg(v_inst_1306_, v___x_1319_);
v___x_1321_ = lean_obj_once(&l_Lean_Expr_updateProjS_x21___redArg___closed__2, &l_Lean_Expr_updateProjS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateProjS_x21___redArg___closed__2);
v___x_1322_ = l_panic___redArg(v___x_1320_, v___x_1321_);
lean_dec(v___x_1320_);
return v___x_1322_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateProjS_x21(lean_object* v_m_1323_, lean_object* v_inst_1324_, lean_object* v_inst_1325_, lean_object* v_e_1326_, lean_object* v_newExpr_1327_){
_start:
{
if (lean_obj_tag(v_e_1326_) == 11)
{
lean_object* v_typeName_1328_; lean_object* v_idx_1329_; lean_object* v_struct_1330_; size_t v___x_1331_; size_t v___x_1332_; uint8_t v___x_1333_; 
v_typeName_1328_ = lean_ctor_get(v_e_1326_, 0);
v_idx_1329_ = lean_ctor_get(v_e_1326_, 1);
v_struct_1330_ = lean_ctor_get(v_e_1326_, 2);
v___x_1331_ = lean_ptr_addr(v_struct_1330_);
v___x_1332_ = lean_ptr_addr(v_newExpr_1327_);
v___x_1333_ = lean_usize_dec_eq(v___x_1331_, v___x_1332_);
if (v___x_1333_ == 0)
{
lean_object* v___x_1334_; 
lean_inc(v_idx_1329_);
lean_inc(v_typeName_1328_);
lean_dec_ref_known(v_e_1326_, 3);
v___x_1334_ = l_Lean_Meta_Sym_Internal_mkProjS___redArg(v_inst_1324_, v_inst_1325_, v_typeName_1328_, v_idx_1329_, v_newExpr_1327_);
return v___x_1334_;
}
else
{
lean_object* v_toApplicative_1335_; lean_object* v_toPure_1336_; lean_object* v___x_1337_; 
lean_dec_ref(v_newExpr_1327_);
lean_dec_ref(v_inst_1324_);
v_toApplicative_1335_ = lean_ctor_get(v_inst_1325_, 0);
lean_inc_ref(v_toApplicative_1335_);
lean_dec_ref(v_inst_1325_);
v_toPure_1336_ = lean_ctor_get(v_toApplicative_1335_, 1);
lean_inc(v_toPure_1336_);
lean_dec_ref(v_toApplicative_1335_);
v___x_1337_ = lean_apply_2(v_toPure_1336_, lean_box(0), v_e_1326_);
return v___x_1337_;
}
}
else
{
lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; 
lean_dec_ref(v_newExpr_1327_);
lean_dec_ref(v_e_1326_);
lean_dec_ref(v_inst_1324_);
v___x_1338_ = l_Lean_instInhabitedExpr;
v___x_1339_ = l_instInhabitedOfMonad___redArg(v_inst_1325_, v___x_1338_);
v___x_1340_ = lean_obj_once(&l_Lean_Expr_updateProjS_x21___redArg___closed__2, &l_Lean_Expr_updateProjS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateProjS_x21___redArg___closed__2);
v___x_1341_ = l_panic___redArg(v___x_1339_, v___x_1340_);
lean_dec(v___x_1339_);
return v___x_1341_;
}
}
}
static lean_object* _init_l_Lean_Expr_updateForallS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; 
v___x_1344_ = ((lean_object*)(l_Lean_Expr_updateForallS_x21___redArg___closed__1));
v___x_1345_ = lean_unsigned_to_nat(31u);
v___x_1346_ = lean_unsigned_to_nat(160u);
v___x_1347_ = ((lean_object*)(l_Lean_Expr_updateForallS_x21___redArg___closed__0));
v___x_1348_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1349_ = l_mkPanicMessageWithDecl(v___x_1348_, v___x_1347_, v___x_1346_, v___x_1345_, v___x_1344_);
return v___x_1349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallS_x21___redArg(lean_object* v_inst_1350_, lean_object* v_inst_1351_, lean_object* v_e_1352_, lean_object* v_newDomain_1353_, lean_object* v_newBody_1354_){
_start:
{
if (lean_obj_tag(v_e_1352_) == 7)
{
lean_object* v_binderName_1355_; lean_object* v_binderType_1356_; lean_object* v_body_1357_; uint8_t v_binderInfo_1358_; uint8_t v___y_1360_; size_t v___x_1365_; size_t v___x_1366_; uint8_t v___x_1367_; 
v_binderName_1355_ = lean_ctor_get(v_e_1352_, 0);
v_binderType_1356_ = lean_ctor_get(v_e_1352_, 1);
v_body_1357_ = lean_ctor_get(v_e_1352_, 2);
v_binderInfo_1358_ = lean_ctor_get_uint8(v_e_1352_, sizeof(void*)*3 + 8);
v___x_1365_ = lean_ptr_addr(v_binderType_1356_);
v___x_1366_ = lean_ptr_addr(v_newDomain_1353_);
v___x_1367_ = lean_usize_dec_eq(v___x_1365_, v___x_1366_);
if (v___x_1367_ == 0)
{
v___y_1360_ = v___x_1367_;
goto v___jp_1359_;
}
else
{
size_t v___x_1368_; size_t v___x_1369_; uint8_t v___x_1370_; 
v___x_1368_ = lean_ptr_addr(v_body_1357_);
v___x_1369_ = lean_ptr_addr(v_newBody_1354_);
v___x_1370_ = lean_usize_dec_eq(v___x_1368_, v___x_1369_);
v___y_1360_ = v___x_1370_;
goto v___jp_1359_;
}
v___jp_1359_:
{
if (v___y_1360_ == 0)
{
lean_object* v___x_1361_; 
lean_inc(v_binderName_1355_);
lean_dec_ref_known(v_e_1352_, 3);
v___x_1361_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v_inst_1350_, v_inst_1351_, v_binderName_1355_, v_binderInfo_1358_, v_newDomain_1353_, v_newBody_1354_);
return v___x_1361_;
}
else
{
lean_object* v_toApplicative_1362_; lean_object* v_toPure_1363_; lean_object* v___x_1364_; 
lean_dec_ref(v_newBody_1354_);
lean_dec_ref(v_newDomain_1353_);
lean_dec_ref(v_inst_1350_);
v_toApplicative_1362_ = lean_ctor_get(v_inst_1351_, 0);
lean_inc_ref(v_toApplicative_1362_);
lean_dec_ref(v_inst_1351_);
v_toPure_1363_ = lean_ctor_get(v_toApplicative_1362_, 1);
lean_inc(v_toPure_1363_);
lean_dec_ref(v_toApplicative_1362_);
v___x_1364_ = lean_apply_2(v_toPure_1363_, lean_box(0), v_e_1352_);
return v___x_1364_;
}
}
}
else
{
lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; 
lean_dec_ref(v_newBody_1354_);
lean_dec_ref(v_newDomain_1353_);
lean_dec_ref(v_e_1352_);
lean_dec_ref(v_inst_1350_);
v___x_1371_ = l_Lean_instInhabitedExpr;
v___x_1372_ = l_instInhabitedOfMonad___redArg(v_inst_1351_, v___x_1371_);
v___x_1373_ = lean_obj_once(&l_Lean_Expr_updateForallS_x21___redArg___closed__2, &l_Lean_Expr_updateForallS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateForallS_x21___redArg___closed__2);
v___x_1374_ = l_panic___redArg(v___x_1372_, v___x_1373_);
lean_dec(v___x_1372_);
return v___x_1374_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallS_x21(lean_object* v_m_1375_, lean_object* v_inst_1376_, lean_object* v_inst_1377_, lean_object* v_e_1378_, lean_object* v_newDomain_1379_, lean_object* v_newBody_1380_){
_start:
{
if (lean_obj_tag(v_e_1378_) == 7)
{
lean_object* v_binderName_1381_; lean_object* v_binderType_1382_; lean_object* v_body_1383_; uint8_t v_binderInfo_1384_; uint8_t v___y_1386_; size_t v___x_1391_; size_t v___x_1392_; uint8_t v___x_1393_; 
v_binderName_1381_ = lean_ctor_get(v_e_1378_, 0);
v_binderType_1382_ = lean_ctor_get(v_e_1378_, 1);
v_body_1383_ = lean_ctor_get(v_e_1378_, 2);
v_binderInfo_1384_ = lean_ctor_get_uint8(v_e_1378_, sizeof(void*)*3 + 8);
v___x_1391_ = lean_ptr_addr(v_binderType_1382_);
v___x_1392_ = lean_ptr_addr(v_newDomain_1379_);
v___x_1393_ = lean_usize_dec_eq(v___x_1391_, v___x_1392_);
if (v___x_1393_ == 0)
{
v___y_1386_ = v___x_1393_;
goto v___jp_1385_;
}
else
{
size_t v___x_1394_; size_t v___x_1395_; uint8_t v___x_1396_; 
v___x_1394_ = lean_ptr_addr(v_body_1383_);
v___x_1395_ = lean_ptr_addr(v_newBody_1380_);
v___x_1396_ = lean_usize_dec_eq(v___x_1394_, v___x_1395_);
v___y_1386_ = v___x_1396_;
goto v___jp_1385_;
}
v___jp_1385_:
{
if (v___y_1386_ == 0)
{
lean_object* v___x_1387_; 
lean_inc(v_binderName_1381_);
lean_dec_ref_known(v_e_1378_, 3);
v___x_1387_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v_inst_1376_, v_inst_1377_, v_binderName_1381_, v_binderInfo_1384_, v_newDomain_1379_, v_newBody_1380_);
return v___x_1387_;
}
else
{
lean_object* v_toApplicative_1388_; lean_object* v_toPure_1389_; lean_object* v___x_1390_; 
lean_dec_ref(v_newBody_1380_);
lean_dec_ref(v_newDomain_1379_);
lean_dec_ref(v_inst_1376_);
v_toApplicative_1388_ = lean_ctor_get(v_inst_1377_, 0);
lean_inc_ref(v_toApplicative_1388_);
lean_dec_ref(v_inst_1377_);
v_toPure_1389_ = lean_ctor_get(v_toApplicative_1388_, 1);
lean_inc(v_toPure_1389_);
lean_dec_ref(v_toApplicative_1388_);
v___x_1390_ = lean_apply_2(v_toPure_1389_, lean_box(0), v_e_1378_);
return v___x_1390_;
}
}
}
else
{
lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; 
lean_dec_ref(v_newBody_1380_);
lean_dec_ref(v_newDomain_1379_);
lean_dec_ref(v_e_1378_);
lean_dec_ref(v_inst_1376_);
v___x_1397_ = l_Lean_instInhabitedExpr;
v___x_1398_ = l_instInhabitedOfMonad___redArg(v_inst_1377_, v___x_1397_);
v___x_1399_ = lean_obj_once(&l_Lean_Expr_updateForallS_x21___redArg___closed__2, &l_Lean_Expr_updateForallS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateForallS_x21___redArg___closed__2);
v___x_1400_ = l_panic___redArg(v___x_1398_, v___x_1399_);
lean_dec(v___x_1398_);
return v___x_1400_;
}
}
}
static lean_object* _init_l_Lean_Expr_updateLambdaS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; 
v___x_1403_ = ((lean_object*)(l_Lean_Expr_updateLambdaS_x21___redArg___closed__1));
v___x_1404_ = lean_unsigned_to_nat(27u);
v___x_1405_ = lean_unsigned_to_nat(167u);
v___x_1406_ = ((lean_object*)(l_Lean_Expr_updateLambdaS_x21___redArg___closed__0));
v___x_1407_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1408_ = l_mkPanicMessageWithDecl(v___x_1407_, v___x_1406_, v___x_1405_, v___x_1404_, v___x_1403_);
return v___x_1408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLambdaS_x21___redArg(lean_object* v_inst_1409_, lean_object* v_inst_1410_, lean_object* v_e_1411_, lean_object* v_newDomain_1412_, lean_object* v_newBody_1413_){
_start:
{
if (lean_obj_tag(v_e_1411_) == 6)
{
lean_object* v_binderName_1414_; lean_object* v_binderType_1415_; lean_object* v_body_1416_; uint8_t v_binderInfo_1417_; uint8_t v___y_1419_; size_t v___x_1424_; size_t v___x_1425_; uint8_t v___x_1426_; 
v_binderName_1414_ = lean_ctor_get(v_e_1411_, 0);
v_binderType_1415_ = lean_ctor_get(v_e_1411_, 1);
v_body_1416_ = lean_ctor_get(v_e_1411_, 2);
v_binderInfo_1417_ = lean_ctor_get_uint8(v_e_1411_, sizeof(void*)*3 + 8);
v___x_1424_ = lean_ptr_addr(v_binderType_1415_);
v___x_1425_ = lean_ptr_addr(v_newDomain_1412_);
v___x_1426_ = lean_usize_dec_eq(v___x_1424_, v___x_1425_);
if (v___x_1426_ == 0)
{
v___y_1419_ = v___x_1426_;
goto v___jp_1418_;
}
else
{
size_t v___x_1427_; size_t v___x_1428_; uint8_t v___x_1429_; 
v___x_1427_ = lean_ptr_addr(v_body_1416_);
v___x_1428_ = lean_ptr_addr(v_newBody_1413_);
v___x_1429_ = lean_usize_dec_eq(v___x_1427_, v___x_1428_);
v___y_1419_ = v___x_1429_;
goto v___jp_1418_;
}
v___jp_1418_:
{
if (v___y_1419_ == 0)
{
lean_object* v___x_1420_; 
lean_inc(v_binderName_1414_);
lean_dec_ref_known(v_e_1411_, 3);
v___x_1420_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v_inst_1409_, v_inst_1410_, v_binderName_1414_, v_binderInfo_1417_, v_newDomain_1412_, v_newBody_1413_);
return v___x_1420_;
}
else
{
lean_object* v_toApplicative_1421_; lean_object* v_toPure_1422_; lean_object* v___x_1423_; 
lean_dec_ref(v_newBody_1413_);
lean_dec_ref(v_newDomain_1412_);
lean_dec_ref(v_inst_1409_);
v_toApplicative_1421_ = lean_ctor_get(v_inst_1410_, 0);
lean_inc_ref(v_toApplicative_1421_);
lean_dec_ref(v_inst_1410_);
v_toPure_1422_ = lean_ctor_get(v_toApplicative_1421_, 1);
lean_inc(v_toPure_1422_);
lean_dec_ref(v_toApplicative_1421_);
v___x_1423_ = lean_apply_2(v_toPure_1422_, lean_box(0), v_e_1411_);
return v___x_1423_;
}
}
}
else
{
lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; 
lean_dec_ref(v_newBody_1413_);
lean_dec_ref(v_newDomain_1412_);
lean_dec_ref(v_e_1411_);
lean_dec_ref(v_inst_1409_);
v___x_1430_ = l_Lean_instInhabitedExpr;
v___x_1431_ = l_instInhabitedOfMonad___redArg(v_inst_1410_, v___x_1430_);
v___x_1432_ = lean_obj_once(&l_Lean_Expr_updateLambdaS_x21___redArg___closed__2, &l_Lean_Expr_updateLambdaS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateLambdaS_x21___redArg___closed__2);
v___x_1433_ = l_panic___redArg(v___x_1431_, v___x_1432_);
lean_dec(v___x_1431_);
return v___x_1433_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLambdaS_x21(lean_object* v_m_1434_, lean_object* v_inst_1435_, lean_object* v_inst_1436_, lean_object* v_e_1437_, lean_object* v_newDomain_1438_, lean_object* v_newBody_1439_){
_start:
{
if (lean_obj_tag(v_e_1437_) == 6)
{
lean_object* v_binderName_1440_; lean_object* v_binderType_1441_; lean_object* v_body_1442_; uint8_t v_binderInfo_1443_; uint8_t v___y_1445_; size_t v___x_1450_; size_t v___x_1451_; uint8_t v___x_1452_; 
v_binderName_1440_ = lean_ctor_get(v_e_1437_, 0);
v_binderType_1441_ = lean_ctor_get(v_e_1437_, 1);
v_body_1442_ = lean_ctor_get(v_e_1437_, 2);
v_binderInfo_1443_ = lean_ctor_get_uint8(v_e_1437_, sizeof(void*)*3 + 8);
v___x_1450_ = lean_ptr_addr(v_binderType_1441_);
v___x_1451_ = lean_ptr_addr(v_newDomain_1438_);
v___x_1452_ = lean_usize_dec_eq(v___x_1450_, v___x_1451_);
if (v___x_1452_ == 0)
{
v___y_1445_ = v___x_1452_;
goto v___jp_1444_;
}
else
{
size_t v___x_1453_; size_t v___x_1454_; uint8_t v___x_1455_; 
v___x_1453_ = lean_ptr_addr(v_body_1442_);
v___x_1454_ = lean_ptr_addr(v_newBody_1439_);
v___x_1455_ = lean_usize_dec_eq(v___x_1453_, v___x_1454_);
v___y_1445_ = v___x_1455_;
goto v___jp_1444_;
}
v___jp_1444_:
{
if (v___y_1445_ == 0)
{
lean_object* v___x_1446_; 
lean_inc(v_binderName_1440_);
lean_dec_ref_known(v_e_1437_, 3);
v___x_1446_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v_inst_1435_, v_inst_1436_, v_binderName_1440_, v_binderInfo_1443_, v_newDomain_1438_, v_newBody_1439_);
return v___x_1446_;
}
else
{
lean_object* v_toApplicative_1447_; lean_object* v_toPure_1448_; lean_object* v___x_1449_; 
lean_dec_ref(v_newBody_1439_);
lean_dec_ref(v_newDomain_1438_);
lean_dec_ref(v_inst_1435_);
v_toApplicative_1447_ = lean_ctor_get(v_inst_1436_, 0);
lean_inc_ref(v_toApplicative_1447_);
lean_dec_ref(v_inst_1436_);
v_toPure_1448_ = lean_ctor_get(v_toApplicative_1447_, 1);
lean_inc(v_toPure_1448_);
lean_dec_ref(v_toApplicative_1447_);
v___x_1449_ = lean_apply_2(v_toPure_1448_, lean_box(0), v_e_1437_);
return v___x_1449_;
}
}
}
else
{
lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; 
lean_dec_ref(v_newBody_1439_);
lean_dec_ref(v_newDomain_1438_);
lean_dec_ref(v_e_1437_);
lean_dec_ref(v_inst_1435_);
v___x_1456_ = l_Lean_instInhabitedExpr;
v___x_1457_ = l_instInhabitedOfMonad___redArg(v_inst_1436_, v___x_1456_);
v___x_1458_ = lean_obj_once(&l_Lean_Expr_updateLambdaS_x21___redArg___closed__2, &l_Lean_Expr_updateLambdaS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateLambdaS_x21___redArg___closed__2);
v___x_1459_ = l_panic___redArg(v___x_1457_, v___x_1458_);
lean_dec(v___x_1457_);
return v___x_1459_;
}
}
}
static lean_object* _init_l_Lean_Expr_updateLetS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; 
v___x_1462_ = ((lean_object*)(l_Lean_Expr_updateLetS_x21___redArg___closed__1));
v___x_1463_ = lean_unsigned_to_nat(34u);
v___x_1464_ = lean_unsigned_to_nat(174u);
v___x_1465_ = ((lean_object*)(l_Lean_Expr_updateLetS_x21___redArg___closed__0));
v___x_1466_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1467_ = l_mkPanicMessageWithDecl(v___x_1466_, v___x_1465_, v___x_1464_, v___x_1463_, v___x_1462_);
return v___x_1467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLetS_x21___redArg(lean_object* v_inst_1468_, lean_object* v_inst_1469_, lean_object* v_e_1470_, lean_object* v_newType_1471_, lean_object* v_newVal_1472_, lean_object* v_newBody_1473_){
_start:
{
if (lean_obj_tag(v_e_1470_) == 8)
{
lean_object* v_declName_1474_; lean_object* v_type_1475_; lean_object* v_value_1476_; lean_object* v_body_1477_; uint8_t v_nondep_1478_; uint8_t v___y_1480_; size_t v___x_1489_; size_t v___x_1490_; uint8_t v___x_1491_; 
v_declName_1474_ = lean_ctor_get(v_e_1470_, 0);
v_type_1475_ = lean_ctor_get(v_e_1470_, 1);
v_value_1476_ = lean_ctor_get(v_e_1470_, 2);
v_body_1477_ = lean_ctor_get(v_e_1470_, 3);
v_nondep_1478_ = lean_ctor_get_uint8(v_e_1470_, sizeof(void*)*4 + 8);
v___x_1489_ = lean_ptr_addr(v_type_1475_);
v___x_1490_ = lean_ptr_addr(v_newType_1471_);
v___x_1491_ = lean_usize_dec_eq(v___x_1489_, v___x_1490_);
if (v___x_1491_ == 0)
{
v___y_1480_ = v___x_1491_;
goto v___jp_1479_;
}
else
{
size_t v___x_1492_; size_t v___x_1493_; uint8_t v___x_1494_; 
v___x_1492_ = lean_ptr_addr(v_value_1476_);
v___x_1493_ = lean_ptr_addr(v_newVal_1472_);
v___x_1494_ = lean_usize_dec_eq(v___x_1492_, v___x_1493_);
v___y_1480_ = v___x_1494_;
goto v___jp_1479_;
}
v___jp_1479_:
{
if (v___y_1480_ == 0)
{
lean_object* v___x_1481_; 
lean_inc(v_declName_1474_);
lean_dec_ref_known(v_e_1470_, 4);
v___x_1481_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1468_, v_inst_1469_, v_declName_1474_, v_newType_1471_, v_newVal_1472_, v_newBody_1473_, v_nondep_1478_);
return v___x_1481_;
}
else
{
size_t v___x_1482_; size_t v___x_1483_; uint8_t v___x_1484_; 
v___x_1482_ = lean_ptr_addr(v_body_1477_);
v___x_1483_ = lean_ptr_addr(v_newBody_1473_);
v___x_1484_ = lean_usize_dec_eq(v___x_1482_, v___x_1483_);
if (v___x_1484_ == 0)
{
lean_object* v___x_1485_; 
lean_inc(v_declName_1474_);
lean_dec_ref_known(v_e_1470_, 4);
v___x_1485_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1468_, v_inst_1469_, v_declName_1474_, v_newType_1471_, v_newVal_1472_, v_newBody_1473_, v_nondep_1478_);
return v___x_1485_;
}
else
{
lean_object* v_toApplicative_1486_; lean_object* v_toPure_1487_; lean_object* v___x_1488_; 
lean_dec_ref(v_newBody_1473_);
lean_dec_ref(v_newVal_1472_);
lean_dec_ref(v_newType_1471_);
lean_dec_ref(v_inst_1468_);
v_toApplicative_1486_ = lean_ctor_get(v_inst_1469_, 0);
lean_inc_ref(v_toApplicative_1486_);
lean_dec_ref(v_inst_1469_);
v_toPure_1487_ = lean_ctor_get(v_toApplicative_1486_, 1);
lean_inc(v_toPure_1487_);
lean_dec_ref(v_toApplicative_1486_);
v___x_1488_ = lean_apply_2(v_toPure_1487_, lean_box(0), v_e_1470_);
return v___x_1488_;
}
}
}
}
else
{
lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; 
lean_dec_ref(v_newBody_1473_);
lean_dec_ref(v_newVal_1472_);
lean_dec_ref(v_newType_1471_);
lean_dec_ref(v_e_1470_);
lean_dec_ref(v_inst_1468_);
v___x_1495_ = l_Lean_instInhabitedExpr;
v___x_1496_ = l_instInhabitedOfMonad___redArg(v_inst_1469_, v___x_1495_);
v___x_1497_ = lean_obj_once(&l_Lean_Expr_updateLetS_x21___redArg___closed__2, &l_Lean_Expr_updateLetS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateLetS_x21___redArg___closed__2);
v___x_1498_ = l_panic___redArg(v___x_1496_, v___x_1497_);
lean_dec(v___x_1496_);
return v___x_1498_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLetS_x21(lean_object* v_m_1499_, lean_object* v_inst_1500_, lean_object* v_inst_1501_, lean_object* v_e_1502_, lean_object* v_newType_1503_, lean_object* v_newVal_1504_, lean_object* v_newBody_1505_){
_start:
{
if (lean_obj_tag(v_e_1502_) == 8)
{
lean_object* v_declName_1506_; lean_object* v_type_1507_; lean_object* v_value_1508_; lean_object* v_body_1509_; uint8_t v_nondep_1510_; uint8_t v___y_1512_; size_t v___x_1521_; size_t v___x_1522_; uint8_t v___x_1523_; 
v_declName_1506_ = lean_ctor_get(v_e_1502_, 0);
v_type_1507_ = lean_ctor_get(v_e_1502_, 1);
v_value_1508_ = lean_ctor_get(v_e_1502_, 2);
v_body_1509_ = lean_ctor_get(v_e_1502_, 3);
v_nondep_1510_ = lean_ctor_get_uint8(v_e_1502_, sizeof(void*)*4 + 8);
v___x_1521_ = lean_ptr_addr(v_type_1507_);
v___x_1522_ = lean_ptr_addr(v_newType_1503_);
v___x_1523_ = lean_usize_dec_eq(v___x_1521_, v___x_1522_);
if (v___x_1523_ == 0)
{
v___y_1512_ = v___x_1523_;
goto v___jp_1511_;
}
else
{
size_t v___x_1524_; size_t v___x_1525_; uint8_t v___x_1526_; 
v___x_1524_ = lean_ptr_addr(v_value_1508_);
v___x_1525_ = lean_ptr_addr(v_newVal_1504_);
v___x_1526_ = lean_usize_dec_eq(v___x_1524_, v___x_1525_);
v___y_1512_ = v___x_1526_;
goto v___jp_1511_;
}
v___jp_1511_:
{
if (v___y_1512_ == 0)
{
lean_object* v___x_1513_; 
lean_inc(v_declName_1506_);
lean_dec_ref_known(v_e_1502_, 4);
v___x_1513_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1500_, v_inst_1501_, v_declName_1506_, v_newType_1503_, v_newVal_1504_, v_newBody_1505_, v_nondep_1510_);
return v___x_1513_;
}
else
{
size_t v___x_1514_; size_t v___x_1515_; uint8_t v___x_1516_; 
v___x_1514_ = lean_ptr_addr(v_body_1509_);
v___x_1515_ = lean_ptr_addr(v_newBody_1505_);
v___x_1516_ = lean_usize_dec_eq(v___x_1514_, v___x_1515_);
if (v___x_1516_ == 0)
{
lean_object* v___x_1517_; 
lean_inc(v_declName_1506_);
lean_dec_ref_known(v_e_1502_, 4);
v___x_1517_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1500_, v_inst_1501_, v_declName_1506_, v_newType_1503_, v_newVal_1504_, v_newBody_1505_, v_nondep_1510_);
return v___x_1517_;
}
else
{
lean_object* v_toApplicative_1518_; lean_object* v_toPure_1519_; lean_object* v___x_1520_; 
lean_dec_ref(v_newBody_1505_);
lean_dec_ref(v_newVal_1504_);
lean_dec_ref(v_newType_1503_);
lean_dec_ref(v_inst_1500_);
v_toApplicative_1518_ = lean_ctor_get(v_inst_1501_, 0);
lean_inc_ref(v_toApplicative_1518_);
lean_dec_ref(v_inst_1501_);
v_toPure_1519_ = lean_ctor_get(v_toApplicative_1518_, 1);
lean_inc(v_toPure_1519_);
lean_dec_ref(v_toApplicative_1518_);
v___x_1520_ = lean_apply_2(v_toPure_1519_, lean_box(0), v_e_1502_);
return v___x_1520_;
}
}
}
}
else
{
lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; 
lean_dec_ref(v_newBody_1505_);
lean_dec_ref(v_newVal_1504_);
lean_dec_ref(v_newType_1503_);
lean_dec_ref(v_e_1502_);
lean_dec_ref(v_inst_1500_);
v___x_1527_ = l_Lean_instInhabitedExpr;
v___x_1528_ = l_instInhabitedOfMonad___redArg(v_inst_1501_, v___x_1527_);
v___x_1529_ = lean_obj_once(&l_Lean_Expr_updateLetS_x21___redArg___closed__2, &l_Lean_Expr_updateLetS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateLetS_x21___redArg___closed__2);
v___x_1530_ = l_panic___redArg(v___x_1528_, v___x_1529_);
lean_dec(v___x_1528_);
return v___x_1530_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___redArg___lam__0(lean_object* v_inst_1531_, lean_object* v_inst_1532_, lean_object* v_a_u2082_1533_, lean_object* v_____do__lift_1534_){
_start:
{
lean_object* v___x_1535_; 
v___x_1535_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1531_, v_inst_1532_, v_____do__lift_1534_, v_a_u2082_1533_);
return v___x_1535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___redArg(lean_object* v_inst_1536_, lean_object* v_inst_1537_, lean_object* v_f_1538_, lean_object* v_a_u2081_1539_, lean_object* v_a_u2082_1540_){
_start:
{
lean_object* v_toBind_1541_; lean_object* v___f_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; 
v_toBind_1541_ = lean_ctor_get(v_inst_1537_, 1);
lean_inc(v_toBind_1541_);
lean_inc_ref(v_inst_1537_);
lean_inc_ref(v_inst_1536_);
v___f_1542_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2082___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1542_, 0, v_inst_1536_);
lean_closure_set(v___f_1542_, 1, v_inst_1537_);
lean_closure_set(v___f_1542_, 2, v_a_u2082_1540_);
v___x_1543_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1536_, v_inst_1537_, v_f_1538_, v_a_u2081_1539_);
v___x_1544_ = lean_apply_4(v_toBind_1541_, lean_box(0), lean_box(0), v___x_1543_, v___f_1542_);
return v___x_1544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082(lean_object* v_m_1545_, lean_object* v_inst_1546_, lean_object* v_inst_1547_, lean_object* v_f_1548_, lean_object* v_a_u2081_1549_, lean_object* v_a_u2082_1550_){
_start:
{
lean_object* v___x_1551_; 
v___x_1551_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___redArg(v_inst_1546_, v_inst_1547_, v_f_1548_, v_a_u2081_1549_, v_a_u2082_1550_);
return v___x_1551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___redArg___lam__0(lean_object* v_inst_1552_, lean_object* v_inst_1553_, lean_object* v_a_u2083_1554_, lean_object* v_____do__lift_1555_){
_start:
{
lean_object* v___x_1556_; 
v___x_1556_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1552_, v_inst_1553_, v_____do__lift_1555_, v_a_u2083_1554_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___redArg(lean_object* v_inst_1557_, lean_object* v_inst_1558_, lean_object* v_f_1559_, lean_object* v_a_u2081_1560_, lean_object* v_a_u2082_1561_, lean_object* v_a_u2083_1562_){
_start:
{
lean_object* v_toBind_1563_; lean_object* v___f_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; 
v_toBind_1563_ = lean_ctor_get(v_inst_1558_, 1);
lean_inc(v_toBind_1563_);
lean_inc_ref(v_inst_1558_);
lean_inc_ref(v_inst_1557_);
v___f_1564_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2083___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1564_, 0, v_inst_1557_);
lean_closure_set(v___f_1564_, 1, v_inst_1558_);
lean_closure_set(v___f_1564_, 2, v_a_u2083_1562_);
v___x_1565_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___redArg(v_inst_1557_, v_inst_1558_, v_f_1559_, v_a_u2081_1560_, v_a_u2082_1561_);
v___x_1566_ = lean_apply_4(v_toBind_1563_, lean_box(0), lean_box(0), v___x_1565_, v___f_1564_);
return v___x_1566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083(lean_object* v_m_1567_, lean_object* v_inst_1568_, lean_object* v_inst_1569_, lean_object* v_f_1570_, lean_object* v_a_u2081_1571_, lean_object* v_a_u2082_1572_, lean_object* v_a_u2083_1573_){
_start:
{
lean_object* v___x_1574_; 
v___x_1574_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___redArg(v_inst_1568_, v_inst_1569_, v_f_1570_, v_a_u2081_1571_, v_a_u2082_1572_, v_a_u2083_1573_);
return v___x_1574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___redArg___lam__0(lean_object* v_inst_1575_, lean_object* v_inst_1576_, lean_object* v_a_u2084_1577_, lean_object* v_____do__lift_1578_){
_start:
{
lean_object* v___x_1579_; 
v___x_1579_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1575_, v_inst_1576_, v_____do__lift_1578_, v_a_u2084_1577_);
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___redArg(lean_object* v_inst_1580_, lean_object* v_inst_1581_, lean_object* v_f_1582_, lean_object* v_a_u2081_1583_, lean_object* v_a_u2082_1584_, lean_object* v_a_u2083_1585_, lean_object* v_a_u2084_1586_){
_start:
{
lean_object* v_toBind_1587_; lean_object* v___f_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; 
v_toBind_1587_ = lean_ctor_get(v_inst_1581_, 1);
lean_inc(v_toBind_1587_);
lean_inc_ref(v_inst_1581_);
lean_inc_ref(v_inst_1580_);
v___f_1588_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2084___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1588_, 0, v_inst_1580_);
lean_closure_set(v___f_1588_, 1, v_inst_1581_);
lean_closure_set(v___f_1588_, 2, v_a_u2084_1586_);
v___x_1589_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___redArg(v_inst_1580_, v_inst_1581_, v_f_1582_, v_a_u2081_1583_, v_a_u2082_1584_, v_a_u2083_1585_);
v___x_1590_ = lean_apply_4(v_toBind_1587_, lean_box(0), lean_box(0), v___x_1589_, v___f_1588_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084(lean_object* v_m_1591_, lean_object* v_inst_1592_, lean_object* v_inst_1593_, lean_object* v_f_1594_, lean_object* v_a_u2081_1595_, lean_object* v_a_u2082_1596_, lean_object* v_a_u2083_1597_, lean_object* v_a_u2084_1598_){
_start:
{
lean_object* v___x_1599_; 
v___x_1599_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___redArg(v_inst_1592_, v_inst_1593_, v_f_1594_, v_a_u2081_1595_, v_a_u2082_1596_, v_a_u2083_1597_, v_a_u2084_1598_);
return v___x_1599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2085___redArg___lam__0(lean_object* v_inst_1600_, lean_object* v_inst_1601_, lean_object* v_a_u2085_1602_, lean_object* v_____do__lift_1603_){
_start:
{
lean_object* v___x_1604_; 
v___x_1604_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1600_, v_inst_1601_, v_____do__lift_1603_, v_a_u2085_1602_);
return v___x_1604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2085___redArg(lean_object* v_inst_1605_, lean_object* v_inst_1606_, lean_object* v_f_1607_, lean_object* v_a_u2081_1608_, lean_object* v_a_u2082_1609_, lean_object* v_a_u2083_1610_, lean_object* v_a_u2084_1611_, lean_object* v_a_u2085_1612_){
_start:
{
lean_object* v_toBind_1613_; lean_object* v___f_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; 
v_toBind_1613_ = lean_ctor_get(v_inst_1606_, 1);
lean_inc(v_toBind_1613_);
lean_inc_ref(v_inst_1606_);
lean_inc_ref(v_inst_1605_);
v___f_1614_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2085___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1614_, 0, v_inst_1605_);
lean_closure_set(v___f_1614_, 1, v_inst_1606_);
lean_closure_set(v___f_1614_, 2, v_a_u2085_1612_);
v___x_1615_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___redArg(v_inst_1605_, v_inst_1606_, v_f_1607_, v_a_u2081_1608_, v_a_u2082_1609_, v_a_u2083_1610_, v_a_u2084_1611_);
v___x_1616_ = lean_apply_4(v_toBind_1613_, lean_box(0), lean_box(0), v___x_1615_, v___f_1614_);
return v___x_1616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2085(lean_object* v_m_1617_, lean_object* v_inst_1618_, lean_object* v_inst_1619_, lean_object* v_f_1620_, lean_object* v_a_u2081_1621_, lean_object* v_a_u2082_1622_, lean_object* v_a_u2083_1623_, lean_object* v_a_u2084_1624_, lean_object* v_a_u2085_1625_){
_start:
{
lean_object* v___x_1626_; 
v___x_1626_ = l_Lean_Meta_Sym_Internal_mkAppS_u2085___redArg(v_inst_1618_, v_inst_1619_, v_f_1620_, v_a_u2081_1621_, v_a_u2082_1622_, v_a_u2083_1623_, v_a_u2084_1624_, v_a_u2085_1625_);
return v___x_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2086___redArg___lam__0(lean_object* v_inst_1627_, lean_object* v_inst_1628_, lean_object* v_a_u2086_1629_, lean_object* v_____do__lift_1630_){
_start:
{
lean_object* v___x_1631_; 
v___x_1631_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1627_, v_inst_1628_, v_____do__lift_1630_, v_a_u2086_1629_);
return v___x_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2086___redArg(lean_object* v_inst_1632_, lean_object* v_inst_1633_, lean_object* v_f_1634_, lean_object* v_a_u2081_1635_, lean_object* v_a_u2082_1636_, lean_object* v_a_u2083_1637_, lean_object* v_a_u2084_1638_, lean_object* v_a_u2085_1639_, lean_object* v_a_u2086_1640_){
_start:
{
lean_object* v_toBind_1641_; lean_object* v___f_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; 
v_toBind_1641_ = lean_ctor_get(v_inst_1633_, 1);
lean_inc(v_toBind_1641_);
lean_inc_ref(v_inst_1633_);
lean_inc_ref(v_inst_1632_);
v___f_1642_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2086___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1642_, 0, v_inst_1632_);
lean_closure_set(v___f_1642_, 1, v_inst_1633_);
lean_closure_set(v___f_1642_, 2, v_a_u2086_1640_);
v___x_1643_ = l_Lean_Meta_Sym_Internal_mkAppS_u2085___redArg(v_inst_1632_, v_inst_1633_, v_f_1634_, v_a_u2081_1635_, v_a_u2082_1636_, v_a_u2083_1637_, v_a_u2084_1638_, v_a_u2085_1639_);
v___x_1644_ = lean_apply_4(v_toBind_1641_, lean_box(0), lean_box(0), v___x_1643_, v___f_1642_);
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2086(lean_object* v_m_1645_, lean_object* v_inst_1646_, lean_object* v_inst_1647_, lean_object* v_f_1648_, lean_object* v_a_u2081_1649_, lean_object* v_a_u2082_1650_, lean_object* v_a_u2083_1651_, lean_object* v_a_u2084_1652_, lean_object* v_a_u2085_1653_, lean_object* v_a_u2086_1654_){
_start:
{
lean_object* v___x_1655_; 
v___x_1655_ = l_Lean_Meta_Sym_Internal_mkAppS_u2086___redArg(v_inst_1646_, v_inst_1647_, v_f_1648_, v_a_u2081_1649_, v_a_u2082_1650_, v_a_u2083_1651_, v_a_u2084_1652_, v_a_u2085_1653_, v_a_u2086_1654_);
return v___x_1655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2087___redArg___lam__0(lean_object* v_inst_1656_, lean_object* v_inst_1657_, lean_object* v_a_u2087_1658_, lean_object* v_____do__lift_1659_){
_start:
{
lean_object* v___x_1660_; 
v___x_1660_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1656_, v_inst_1657_, v_____do__lift_1659_, v_a_u2087_1658_);
return v___x_1660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2087___redArg(lean_object* v_inst_1661_, lean_object* v_inst_1662_, lean_object* v_f_1663_, lean_object* v_a_u2081_1664_, lean_object* v_a_u2082_1665_, lean_object* v_a_u2083_1666_, lean_object* v_a_u2084_1667_, lean_object* v_a_u2085_1668_, lean_object* v_a_u2086_1669_, lean_object* v_a_u2087_1670_){
_start:
{
lean_object* v_toBind_1671_; lean_object* v___f_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; 
v_toBind_1671_ = lean_ctor_get(v_inst_1662_, 1);
lean_inc(v_toBind_1671_);
lean_inc_ref(v_inst_1662_);
lean_inc_ref(v_inst_1661_);
v___f_1672_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2087___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1672_, 0, v_inst_1661_);
lean_closure_set(v___f_1672_, 1, v_inst_1662_);
lean_closure_set(v___f_1672_, 2, v_a_u2087_1670_);
v___x_1673_ = l_Lean_Meta_Sym_Internal_mkAppS_u2086___redArg(v_inst_1661_, v_inst_1662_, v_f_1663_, v_a_u2081_1664_, v_a_u2082_1665_, v_a_u2083_1666_, v_a_u2084_1667_, v_a_u2085_1668_, v_a_u2086_1669_);
v___x_1674_ = lean_apply_4(v_toBind_1671_, lean_box(0), lean_box(0), v___x_1673_, v___f_1672_);
return v___x_1674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2087(lean_object* v_m_1675_, lean_object* v_inst_1676_, lean_object* v_inst_1677_, lean_object* v_f_1678_, lean_object* v_a_u2081_1679_, lean_object* v_a_u2082_1680_, lean_object* v_a_u2083_1681_, lean_object* v_a_u2084_1682_, lean_object* v_a_u2085_1683_, lean_object* v_a_u2086_1684_, lean_object* v_a_u2087_1685_){
_start:
{
lean_object* v___x_1686_; 
v___x_1686_ = l_Lean_Meta_Sym_Internal_mkAppS_u2087___redArg(v_inst_1676_, v_inst_1677_, v_f_1678_, v_a_u2081_1679_, v_a_u2082_1680_, v_a_u2083_1681_, v_a_u2084_1682_, v_a_u2085_1683_, v_a_u2086_1684_, v_a_u2087_1685_);
return v___x_1686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2088___redArg___lam__0(lean_object* v_inst_1687_, lean_object* v_inst_1688_, lean_object* v_a_u2088_1689_, lean_object* v_____do__lift_1690_){
_start:
{
lean_object* v___x_1691_; 
v___x_1691_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1687_, v_inst_1688_, v_____do__lift_1690_, v_a_u2088_1689_);
return v___x_1691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2088___redArg(lean_object* v_inst_1692_, lean_object* v_inst_1693_, lean_object* v_f_1694_, lean_object* v_a_u2081_1695_, lean_object* v_a_u2082_1696_, lean_object* v_a_u2083_1697_, lean_object* v_a_u2084_1698_, lean_object* v_a_u2085_1699_, lean_object* v_a_u2086_1700_, lean_object* v_a_u2087_1701_, lean_object* v_a_u2088_1702_){
_start:
{
lean_object* v_toBind_1703_; lean_object* v___f_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; 
v_toBind_1703_ = lean_ctor_get(v_inst_1693_, 1);
lean_inc(v_toBind_1703_);
lean_inc_ref(v_inst_1693_);
lean_inc_ref(v_inst_1692_);
v___f_1704_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2088___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1704_, 0, v_inst_1692_);
lean_closure_set(v___f_1704_, 1, v_inst_1693_);
lean_closure_set(v___f_1704_, 2, v_a_u2088_1702_);
v___x_1705_ = l_Lean_Meta_Sym_Internal_mkAppS_u2087___redArg(v_inst_1692_, v_inst_1693_, v_f_1694_, v_a_u2081_1695_, v_a_u2082_1696_, v_a_u2083_1697_, v_a_u2084_1698_, v_a_u2085_1699_, v_a_u2086_1700_, v_a_u2087_1701_);
v___x_1706_ = lean_apply_4(v_toBind_1703_, lean_box(0), lean_box(0), v___x_1705_, v___f_1704_);
return v___x_1706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2088(lean_object* v_m_1707_, lean_object* v_inst_1708_, lean_object* v_inst_1709_, lean_object* v_f_1710_, lean_object* v_a_u2081_1711_, lean_object* v_a_u2082_1712_, lean_object* v_a_u2083_1713_, lean_object* v_a_u2084_1714_, lean_object* v_a_u2085_1715_, lean_object* v_a_u2086_1716_, lean_object* v_a_u2087_1717_, lean_object* v_a_u2088_1718_){
_start:
{
lean_object* v___x_1719_; 
v___x_1719_ = l_Lean_Meta_Sym_Internal_mkAppS_u2088___redArg(v_inst_1708_, v_inst_1709_, v_f_1710_, v_a_u2081_1711_, v_a_u2082_1712_, v_a_u2083_1713_, v_a_u2084_1714_, v_a_u2085_1715_, v_a_u2086_1716_, v_a_u2087_1717_, v_a_u2088_1718_);
return v___x_1719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2089___redArg___lam__0(lean_object* v_inst_1720_, lean_object* v_inst_1721_, lean_object* v_a_u2089_1722_, lean_object* v_____do__lift_1723_){
_start:
{
lean_object* v___x_1724_; 
v___x_1724_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1720_, v_inst_1721_, v_____do__lift_1723_, v_a_u2089_1722_);
return v___x_1724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2089___redArg(lean_object* v_inst_1725_, lean_object* v_inst_1726_, lean_object* v_f_1727_, lean_object* v_a_u2081_1728_, lean_object* v_a_u2082_1729_, lean_object* v_a_u2083_1730_, lean_object* v_a_u2084_1731_, lean_object* v_a_u2085_1732_, lean_object* v_a_u2086_1733_, lean_object* v_a_u2087_1734_, lean_object* v_a_u2088_1735_, lean_object* v_a_u2089_1736_){
_start:
{
lean_object* v_toBind_1737_; lean_object* v___f_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; 
v_toBind_1737_ = lean_ctor_get(v_inst_1726_, 1);
lean_inc(v_toBind_1737_);
lean_inc_ref(v_inst_1726_);
lean_inc_ref(v_inst_1725_);
v___f_1738_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2089___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1738_, 0, v_inst_1725_);
lean_closure_set(v___f_1738_, 1, v_inst_1726_);
lean_closure_set(v___f_1738_, 2, v_a_u2089_1736_);
v___x_1739_ = l_Lean_Meta_Sym_Internal_mkAppS_u2088___redArg(v_inst_1725_, v_inst_1726_, v_f_1727_, v_a_u2081_1728_, v_a_u2082_1729_, v_a_u2083_1730_, v_a_u2084_1731_, v_a_u2085_1732_, v_a_u2086_1733_, v_a_u2087_1734_, v_a_u2088_1735_);
v___x_1740_ = lean_apply_4(v_toBind_1737_, lean_box(0), lean_box(0), v___x_1739_, v___f_1738_);
return v___x_1740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2089(lean_object* v_m_1741_, lean_object* v_inst_1742_, lean_object* v_inst_1743_, lean_object* v_f_1744_, lean_object* v_a_u2081_1745_, lean_object* v_a_u2082_1746_, lean_object* v_a_u2083_1747_, lean_object* v_a_u2084_1748_, lean_object* v_a_u2085_1749_, lean_object* v_a_u2086_1750_, lean_object* v_a_u2087_1751_, lean_object* v_a_u2088_1752_, lean_object* v_a_u2089_1753_){
_start:
{
lean_object* v___x_1754_; 
v___x_1754_ = l_Lean_Meta_Sym_Internal_mkAppS_u2089___redArg(v_inst_1742_, v_inst_1743_, v_f_1744_, v_a_u2081_1745_, v_a_u2082_1746_, v_a_u2083_1747_, v_a_u2084_1748_, v_a_u2085_1749_, v_a_u2086_1750_, v_a_u2087_1751_, v_a_u2088_1752_, v_a_u2089_1753_);
return v___x_1754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2080___redArg___lam__0(lean_object* v_inst_1755_, lean_object* v_inst_1756_, lean_object* v_a_u2081_u2080_1757_, lean_object* v_____do__lift_1758_){
_start:
{
lean_object* v___x_1759_; 
v___x_1759_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1755_, v_inst_1756_, v_____do__lift_1758_, v_a_u2081_u2080_1757_);
return v___x_1759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2080___redArg(lean_object* v_inst_1760_, lean_object* v_inst_1761_, lean_object* v_f_1762_, lean_object* v_a_u2081_1763_, lean_object* v_a_u2082_1764_, lean_object* v_a_u2083_1765_, lean_object* v_a_u2084_1766_, lean_object* v_a_u2085_1767_, lean_object* v_a_u2086_1768_, lean_object* v_a_u2087_1769_, lean_object* v_a_u2088_1770_, lean_object* v_a_u2089_1771_, lean_object* v_a_u2081_u2080_1772_){
_start:
{
lean_object* v_toBind_1773_; lean_object* v___f_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; 
v_toBind_1773_ = lean_ctor_get(v_inst_1761_, 1);
lean_inc(v_toBind_1773_);
lean_inc_ref(v_inst_1761_);
lean_inc_ref(v_inst_1760_);
v___f_1774_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2080___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1774_, 0, v_inst_1760_);
lean_closure_set(v___f_1774_, 1, v_inst_1761_);
lean_closure_set(v___f_1774_, 2, v_a_u2081_u2080_1772_);
v___x_1775_ = l_Lean_Meta_Sym_Internal_mkAppS_u2089___redArg(v_inst_1760_, v_inst_1761_, v_f_1762_, v_a_u2081_1763_, v_a_u2082_1764_, v_a_u2083_1765_, v_a_u2084_1766_, v_a_u2085_1767_, v_a_u2086_1768_, v_a_u2087_1769_, v_a_u2088_1770_, v_a_u2089_1771_);
v___x_1776_ = lean_apply_4(v_toBind_1773_, lean_box(0), lean_box(0), v___x_1775_, v___f_1774_);
return v___x_1776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2080(lean_object* v_m_1777_, lean_object* v_inst_1778_, lean_object* v_inst_1779_, lean_object* v_f_1780_, lean_object* v_a_u2081_1781_, lean_object* v_a_u2082_1782_, lean_object* v_a_u2083_1783_, lean_object* v_a_u2084_1784_, lean_object* v_a_u2085_1785_, lean_object* v_a_u2086_1786_, lean_object* v_a_u2087_1787_, lean_object* v_a_u2088_1788_, lean_object* v_a_u2089_1789_, lean_object* v_a_u2081_u2080_1790_){
_start:
{
lean_object* v___x_1791_; 
v___x_1791_ = l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2080___redArg(v_inst_1778_, v_inst_1779_, v_f_1780_, v_a_u2081_1781_, v_a_u2082_1782_, v_a_u2083_1783_, v_a_u2084_1784_, v_a_u2085_1785_, v_a_u2086_1786_, v_a_u2087_1787_, v_a_u2088_1788_, v_a_u2089_1789_, v_a_u2081_u2080_1790_);
return v___x_1791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2081___redArg___lam__0(lean_object* v_inst_1792_, lean_object* v_inst_1793_, lean_object* v_a_u2081_u2081_1794_, lean_object* v_____do__lift_1795_){
_start:
{
lean_object* v___x_1796_; 
v___x_1796_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1792_, v_inst_1793_, v_____do__lift_1795_, v_a_u2081_u2081_1794_);
return v___x_1796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2081___redArg(lean_object* v_inst_1797_, lean_object* v_inst_1798_, lean_object* v_f_1799_, lean_object* v_a_u2081_1800_, lean_object* v_a_u2082_1801_, lean_object* v_a_u2083_1802_, lean_object* v_a_u2084_1803_, lean_object* v_a_u2085_1804_, lean_object* v_a_u2086_1805_, lean_object* v_a_u2087_1806_, lean_object* v_a_u2088_1807_, lean_object* v_a_u2089_1808_, lean_object* v_a_u2081_u2080_1809_, lean_object* v_a_u2081_u2081_1810_){
_start:
{
lean_object* v_toBind_1811_; lean_object* v___f_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; 
v_toBind_1811_ = lean_ctor_get(v_inst_1798_, 1);
lean_inc(v_toBind_1811_);
lean_inc_ref(v_inst_1798_);
lean_inc_ref(v_inst_1797_);
v___f_1812_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2081___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1812_, 0, v_inst_1797_);
lean_closure_set(v___f_1812_, 1, v_inst_1798_);
lean_closure_set(v___f_1812_, 2, v_a_u2081_u2081_1810_);
v___x_1813_ = l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2080___redArg(v_inst_1797_, v_inst_1798_, v_f_1799_, v_a_u2081_1800_, v_a_u2082_1801_, v_a_u2083_1802_, v_a_u2084_1803_, v_a_u2085_1804_, v_a_u2086_1805_, v_a_u2087_1806_, v_a_u2088_1807_, v_a_u2089_1808_, v_a_u2081_u2080_1809_);
v___x_1814_ = lean_apply_4(v_toBind_1811_, lean_box(0), lean_box(0), v___x_1813_, v___f_1812_);
return v___x_1814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2081(lean_object* v_m_1815_, lean_object* v_inst_1816_, lean_object* v_inst_1817_, lean_object* v_f_1818_, lean_object* v_a_u2081_1819_, lean_object* v_a_u2082_1820_, lean_object* v_a_u2083_1821_, lean_object* v_a_u2084_1822_, lean_object* v_a_u2085_1823_, lean_object* v_a_u2086_1824_, lean_object* v_a_u2087_1825_, lean_object* v_a_u2088_1826_, lean_object* v_a_u2089_1827_, lean_object* v_a_u2081_u2080_1828_, lean_object* v_a_u2081_u2081_1829_){
_start:
{
lean_object* v___x_1830_; 
v___x_1830_ = l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2081___redArg(v_inst_1816_, v_inst_1817_, v_f_1818_, v_a_u2081_1819_, v_a_u2082_1820_, v_a_u2083_1821_, v_a_u2084_1822_, v_a_u2085_1823_, v_a_u2086_1824_, v_a_u2087_1825_, v_a_u2088_1826_, v_a_u2089_1827_, v_a_u2081_u2080_1828_, v_a_u2081_u2081_1829_);
return v___x_1830_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg___lam__0___boxed(lean_object* v_i_1831_, lean_object* v_inst_1832_, lean_object* v_inst_1833_, lean_object* v_args_1834_, lean_object* v_endIdx_1835_, lean_object* v_____do__lift_1836_){
_start:
{
lean_object* v_res_1837_; 
v_res_1837_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg___lam__0(v_i_1831_, v_inst_1832_, v_inst_1833_, v_args_1834_, v_endIdx_1835_, v_____do__lift_1836_);
lean_dec(v_i_1831_);
return v_res_1837_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg(lean_object* v_inst_1838_, lean_object* v_inst_1839_, lean_object* v_args_1840_, lean_object* v_endIdx_1841_, lean_object* v_b_1842_, lean_object* v_i_1843_){
_start:
{
uint8_t v___x_1844_; 
v___x_1844_ = lean_nat_dec_le(v_endIdx_1841_, v_i_1843_);
if (v___x_1844_ == 0)
{
lean_object* v_toBind_1845_; lean_object* v___f_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; 
v_toBind_1845_ = lean_ctor_get(v_inst_1839_, 1);
lean_inc(v_toBind_1845_);
lean_inc_ref(v_args_1840_);
lean_inc_ref(v_inst_1839_);
lean_inc_ref(v_inst_1838_);
lean_inc(v_i_1843_);
v___f_1846_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1846_, 0, v_i_1843_);
lean_closure_set(v___f_1846_, 1, v_inst_1838_);
lean_closure_set(v___f_1846_, 2, v_inst_1839_);
lean_closure_set(v___f_1846_, 3, v_args_1840_);
lean_closure_set(v___f_1846_, 4, v_endIdx_1841_);
v___x_1847_ = l_Lean_instInhabitedExpr;
v___x_1848_ = lean_array_get(v___x_1847_, v_args_1840_, v_i_1843_);
lean_dec(v_i_1843_);
lean_dec_ref(v_args_1840_);
v___x_1849_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1838_, v_inst_1839_, v_b_1842_, v___x_1848_);
v___x_1850_ = lean_apply_4(v_toBind_1845_, lean_box(0), lean_box(0), v___x_1849_, v___f_1846_);
return v___x_1850_;
}
else
{
lean_object* v_toApplicative_1851_; lean_object* v_toPure_1852_; lean_object* v___x_1853_; 
lean_dec(v_i_1843_);
lean_dec(v_endIdx_1841_);
lean_dec_ref(v_args_1840_);
lean_dec_ref(v_inst_1838_);
v_toApplicative_1851_ = lean_ctor_get(v_inst_1839_, 0);
lean_inc_ref(v_toApplicative_1851_);
lean_dec_ref(v_inst_1839_);
v_toPure_1852_ = lean_ctor_get(v_toApplicative_1851_, 1);
lean_inc(v_toPure_1852_);
lean_dec_ref(v_toApplicative_1851_);
v___x_1853_ = lean_apply_2(v_toPure_1852_, lean_box(0), v_b_1842_);
return v___x_1853_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg___lam__0(lean_object* v_i_1854_, lean_object* v_inst_1855_, lean_object* v_inst_1856_, lean_object* v_args_1857_, lean_object* v_endIdx_1858_, lean_object* v_____do__lift_1859_){
_start:
{
lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; 
v___x_1860_ = lean_unsigned_to_nat(1u);
v___x_1861_ = lean_nat_add(v_i_1854_, v___x_1860_);
v___x_1862_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg(v_inst_1855_, v_inst_1856_, v_args_1857_, v_endIdx_1858_, v_____do__lift_1859_, v___x_1861_);
return v___x_1862_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go(lean_object* v_m_1863_, lean_object* v_inst_1864_, lean_object* v_inst_1865_, lean_object* v_args_1866_, lean_object* v_endIdx_1867_, lean_object* v_b_1868_, lean_object* v_i_1869_){
_start:
{
lean_object* v___x_1870_; 
v___x_1870_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg(v_inst_1864_, v_inst_1865_, v_args_1866_, v_endIdx_1867_, v_b_1868_, v_i_1869_);
return v___x_1870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRangeS___redArg(lean_object* v_inst_1871_, lean_object* v_inst_1872_, lean_object* v_f_1873_, lean_object* v_beginIdx_1874_, lean_object* v_endIdx_1875_, lean_object* v_args_1876_){
_start:
{
lean_object* v___x_1877_; 
v___x_1877_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg(v_inst_1871_, v_inst_1872_, v_args_1876_, v_endIdx_1875_, v_f_1873_, v_beginIdx_1874_);
return v___x_1877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRangeS(lean_object* v_m_1878_, lean_object* v_inst_1879_, lean_object* v_inst_1880_, lean_object* v_f_1881_, lean_object* v_beginIdx_1882_, lean_object* v_endIdx_1883_, lean_object* v_args_1884_){
_start:
{
lean_object* v___x_1885_; 
v___x_1885_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg(v_inst_1879_, v_inst_1880_, v_args_1884_, v_endIdx_1883_, v_f_1881_, v_beginIdx_1882_);
return v___x_1885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___redArg(lean_object* v_inst_1886_, lean_object* v_inst_1887_, lean_object* v_f_1888_, lean_object* v_args_1889_){
_start:
{
lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; 
v___x_1890_ = lean_unsigned_to_nat(0u);
v___x_1891_ = lean_array_get_size(v_args_1889_);
v___x_1892_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg(v_inst_1886_, v_inst_1887_, v_args_1889_, v___x_1891_, v_f_1888_, v___x_1890_);
return v___x_1892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS(lean_object* v_m_1893_, lean_object* v_inst_1894_, lean_object* v_inst_1895_, lean_object* v_f_1896_, lean_object* v_args_1897_){
_start:
{
lean_object* v___x_1898_; 
v___x_1898_ = l_Lean_Meta_Sym_Internal_mkAppNS___redArg(v_inst_1894_, v_inst_1895_, v_f_1896_, v_args_1897_);
return v___x_1898_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg___lam__0___boxed(lean_object* v_inst_1899_, lean_object* v_inst_1900_, lean_object* v_revArgs_1901_, lean_object* v_start_1902_, lean_object* v_i_1903_, lean_object* v_____do__lift_1904_){
_start:
{
lean_object* v_res_1905_; 
v_res_1905_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg___lam__0(v_inst_1899_, v_inst_1900_, v_revArgs_1901_, v_start_1902_, v_i_1903_, v_____do__lift_1904_);
lean_dec(v_i_1903_);
return v_res_1905_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg(lean_object* v_inst_1906_, lean_object* v_inst_1907_, lean_object* v_revArgs_1908_, lean_object* v_start_1909_, lean_object* v_b_1910_, lean_object* v_i_1911_){
_start:
{
uint8_t v___x_1912_; 
v___x_1912_ = lean_nat_dec_le(v_i_1911_, v_start_1909_);
if (v___x_1912_ == 0)
{
lean_object* v_toBind_1913_; lean_object* v___x_1914_; lean_object* v_i_1915_; lean_object* v___f_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; 
v_toBind_1913_ = lean_ctor_get(v_inst_1907_, 1);
lean_inc(v_toBind_1913_);
v___x_1914_ = lean_unsigned_to_nat(1u);
v_i_1915_ = lean_nat_sub(v_i_1911_, v___x_1914_);
lean_inc(v_i_1915_);
lean_inc_ref(v_revArgs_1908_);
lean_inc_ref(v_inst_1907_);
lean_inc_ref(v_inst_1906_);
v___f_1916_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1916_, 0, v_inst_1906_);
lean_closure_set(v___f_1916_, 1, v_inst_1907_);
lean_closure_set(v___f_1916_, 2, v_revArgs_1908_);
lean_closure_set(v___f_1916_, 3, v_start_1909_);
lean_closure_set(v___f_1916_, 4, v_i_1915_);
v___x_1917_ = l_Lean_instInhabitedExpr;
v___x_1918_ = lean_array_get(v___x_1917_, v_revArgs_1908_, v_i_1915_);
lean_dec(v_i_1915_);
lean_dec_ref(v_revArgs_1908_);
v___x_1919_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1906_, v_inst_1907_, v_b_1910_, v___x_1918_);
v___x_1920_ = lean_apply_4(v_toBind_1913_, lean_box(0), lean_box(0), v___x_1919_, v___f_1916_);
return v___x_1920_;
}
else
{
lean_object* v_toApplicative_1921_; lean_object* v_toPure_1922_; lean_object* v___x_1923_; 
lean_dec(v_start_1909_);
lean_dec_ref(v_revArgs_1908_);
lean_dec_ref(v_inst_1906_);
v_toApplicative_1921_ = lean_ctor_get(v_inst_1907_, 0);
lean_inc_ref(v_toApplicative_1921_);
lean_dec_ref(v_inst_1907_);
v_toPure_1922_ = lean_ctor_get(v_toApplicative_1921_, 1);
lean_inc(v_toPure_1922_);
lean_dec_ref(v_toApplicative_1921_);
v___x_1923_ = lean_apply_2(v_toPure_1922_, lean_box(0), v_b_1910_);
return v___x_1923_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg___lam__0(lean_object* v_inst_1924_, lean_object* v_inst_1925_, lean_object* v_revArgs_1926_, lean_object* v_start_1927_, lean_object* v_i_1928_, lean_object* v_____do__lift_1929_){
_start:
{
lean_object* v___x_1930_; 
v___x_1930_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg(v_inst_1924_, v_inst_1925_, v_revArgs_1926_, v_start_1927_, v_____do__lift_1929_, v_i_1928_);
return v___x_1930_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg___boxed(lean_object* v_inst_1931_, lean_object* v_inst_1932_, lean_object* v_revArgs_1933_, lean_object* v_start_1934_, lean_object* v_b_1935_, lean_object* v_i_1936_){
_start:
{
lean_object* v_res_1937_; 
v_res_1937_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg(v_inst_1931_, v_inst_1932_, v_revArgs_1933_, v_start_1934_, v_b_1935_, v_i_1936_);
lean_dec(v_i_1936_);
return v_res_1937_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go(lean_object* v_m_1938_, lean_object* v_inst_1939_, lean_object* v_inst_1940_, lean_object* v_revArgs_1941_, lean_object* v_start_1942_, lean_object* v_b_1943_, lean_object* v_i_1944_){
_start:
{
lean_object* v___x_1945_; 
v___x_1945_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg(v_inst_1939_, v_inst_1940_, v_revArgs_1941_, v_start_1942_, v_b_1943_, v_i_1944_);
return v___x_1945_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___boxed(lean_object* v_m_1946_, lean_object* v_inst_1947_, lean_object* v_inst_1948_, lean_object* v_revArgs_1949_, lean_object* v_start_1950_, lean_object* v_b_1951_, lean_object* v_i_1952_){
_start:
{
lean_object* v_res_1953_; 
v_res_1953_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go(v_m_1946_, v_inst_1947_, v_inst_1948_, v_revArgs_1949_, v_start_1950_, v_b_1951_, v_i_1952_);
lean_dec(v_i_1952_);
return v_res_1953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevRangeS___redArg(lean_object* v_inst_1954_, lean_object* v_inst_1955_, lean_object* v_f_1956_, lean_object* v_beginIdx_1957_, lean_object* v_endIdx_1958_, lean_object* v_revArgs_1959_){
_start:
{
lean_object* v___x_1960_; 
v___x_1960_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg(v_inst_1954_, v_inst_1955_, v_revArgs_1959_, v_beginIdx_1957_, v_f_1956_, v_endIdx_1958_);
return v___x_1960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevRangeS___redArg___boxed(lean_object* v_inst_1961_, lean_object* v_inst_1962_, lean_object* v_f_1963_, lean_object* v_beginIdx_1964_, lean_object* v_endIdx_1965_, lean_object* v_revArgs_1966_){
_start:
{
lean_object* v_res_1967_; 
v_res_1967_ = l_Lean_Meta_Sym_Internal_mkAppRevRangeS___redArg(v_inst_1961_, v_inst_1962_, v_f_1963_, v_beginIdx_1964_, v_endIdx_1965_, v_revArgs_1966_);
lean_dec(v_endIdx_1965_);
return v_res_1967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevRangeS(lean_object* v_m_1968_, lean_object* v_inst_1969_, lean_object* v_inst_1970_, lean_object* v_f_1971_, lean_object* v_beginIdx_1972_, lean_object* v_endIdx_1973_, lean_object* v_revArgs_1974_){
_start:
{
lean_object* v___x_1975_; 
v___x_1975_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg(v_inst_1969_, v_inst_1970_, v_revArgs_1974_, v_beginIdx_1972_, v_f_1971_, v_endIdx_1973_);
return v___x_1975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevRangeS___boxed(lean_object* v_m_1976_, lean_object* v_inst_1977_, lean_object* v_inst_1978_, lean_object* v_f_1979_, lean_object* v_beginIdx_1980_, lean_object* v_endIdx_1981_, lean_object* v_revArgs_1982_){
_start:
{
lean_object* v_res_1983_; 
v_res_1983_ = l_Lean_Meta_Sym_Internal_mkAppRevRangeS(v_m_1976_, v_inst_1977_, v_inst_1978_, v_f_1979_, v_beginIdx_1980_, v_endIdx_1981_, v_revArgs_1982_);
lean_dec(v_endIdx_1981_);
return v_res_1983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevS___redArg(lean_object* v_inst_1984_, lean_object* v_inst_1985_, lean_object* v_f_1986_, lean_object* v_revArgs_1987_){
_start:
{
lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; 
v___x_1988_ = lean_unsigned_to_nat(0u);
v___x_1989_ = lean_array_get_size(v_revArgs_1987_);
v___x_1990_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg(v_inst_1984_, v_inst_1985_, v_revArgs_1987_, v___x_1988_, v_f_1986_, v___x_1989_);
return v___x_1990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevS(lean_object* v_m_1991_, lean_object* v_inst_1992_, lean_object* v_inst_1993_, lean_object* v_f_1994_, lean_object* v_revArgs_1995_){
_start:
{
lean_object* v___x_1996_; 
v___x_1996_ = l_Lean_Meta_Sym_Internal_mkAppRevS___redArg(v_inst_1992_, v_inst_1993_, v_f_1994_, v_revArgs_1995_);
return v___x_1996_;
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
