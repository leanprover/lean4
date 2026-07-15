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
lean_object* l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_hashPtrExpr_unsafe__1___boxed(lean_object*);
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
static const lean_closure_object l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__0 = (const lean_object*)&l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__0_value;
static const lean_closure_object l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_hashPtrExpr_unsafe__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
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
size_t v_x_2167__boxed_191_; size_t v_x_2168__boxed_192_; lean_object* v_res_193_; 
v_x_2167__boxed_191_ = lean_unbox_usize(v_x_187_);
lean_dec(v_x_187_);
v_x_2168__boxed_192_ = lean_unbox_usize(v_x_188_);
lean_dec(v_x_188_);
v_res_193_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg(v_x_186_, v_x_2167__boxed_191_, v_x_2168__boxed_192_, v_x_189_, v_x_190_);
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
size_t v_x_2349__boxed_240_; lean_object* v_res_241_; 
v_x_2349__boxed_240_ = lean_unbox_usize(v_x_237_);
lean_dec(v_x_237_);
v_res_241_ = l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg(v_x_236_, v_x_2349__boxed_240_, v_x_238_, v_x_239_);
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
lean_object* v___x_253_; lean_object* v_share_254_; lean_object* v_maxFVar_255_; lean_object* v_proofInstInfo_256_; lean_object* v_inferType_257_; lean_object* v_getLevel_258_; lean_object* v_congrInfo_259_; lean_object* v_defEqI_260_; lean_object* v_extensions_261_; lean_object* v_issues_262_; lean_object* v_canon_263_; lean_object* v_instanceOverrides_264_; uint8_t v_debug_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_276_; 
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
v_instanceOverrides_264_ = lean_ctor_get(v___x_253_, 10);
v_debug_265_ = lean_ctor_get_uint8(v___x_253_, sizeof(void*)*11);
v_isSharedCheck_276_ = !lean_is_exclusive(v___x_253_);
if (v_isSharedCheck_276_ == 0)
{
v___x_267_ = v___x_253_;
v_isShared_268_ = v_isSharedCheck_276_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_instanceOverrides_264_);
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
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_276_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_272_; 
v___x_269_ = lean_box(0);
lean_inc_ref(v_e_242_);
v___x_270_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1___redArg(v_share_254_, v_e_242_, v___x_269_);
if (v_isShared_268_ == 0)
{
lean_ctor_set(v___x_267_, 0, v___x_270_);
v___x_272_ = v___x_267_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v___x_270_);
lean_ctor_set(v_reuseFailAlloc_275_, 1, v_maxFVar_255_);
lean_ctor_set(v_reuseFailAlloc_275_, 2, v_proofInstInfo_256_);
lean_ctor_set(v_reuseFailAlloc_275_, 3, v_inferType_257_);
lean_ctor_set(v_reuseFailAlloc_275_, 4, v_getLevel_258_);
lean_ctor_set(v_reuseFailAlloc_275_, 5, v_congrInfo_259_);
lean_ctor_set(v_reuseFailAlloc_275_, 6, v_defEqI_260_);
lean_ctor_set(v_reuseFailAlloc_275_, 7, v_extensions_261_);
lean_ctor_set(v_reuseFailAlloc_275_, 8, v_issues_262_);
lean_ctor_set(v_reuseFailAlloc_275_, 9, v_canon_263_);
lean_ctor_set(v_reuseFailAlloc_275_, 10, v_instanceOverrides_264_);
lean_ctor_set_uint8(v_reuseFailAlloc_275_, sizeof(void*)*11, v_debug_265_);
v___x_272_ = v_reuseFailAlloc_275_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_273_ = lean_st_ref_set(v_a_243_, v___x_272_);
v___x_274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_274_, 0, v_e_242_);
return v___x_274_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg___boxed(lean_object* v_e_277_, lean_object* v_a_278_, lean_object* v_a_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v_e_277_, v_a_278_);
lean_dec(v_a_278_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Sym_share1(lean_object* v_e_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_){
_start:
{
lean_object* v___x_289_; 
v___x_289_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v_e_281_, v_a_283_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___boxed(lean_object* v_e_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_Lean_Meta_Sym_Internal_Sym_share1(v_e_290_, v_a_291_, v_a_292_, v_a_293_, v_a_294_, v_a_295_, v_a_296_);
lean_dec(v_a_296_);
lean_dec_ref(v_a_295_);
lean_dec(v_a_294_);
lean_dec_ref(v_a_293_);
lean_dec(v_a_292_);
lean_dec_ref(v_a_291_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0(lean_object* v_00_u03b2_299_, lean_object* v_x_300_, size_t v_x_301_, lean_object* v_x_302_, lean_object* v_x_303_){
_start:
{
lean_object* v___x_304_; 
v___x_304_ = l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg(v_x_300_, v_x_301_, v_x_302_, v_x_303_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___boxed(lean_object* v_00_u03b2_305_, lean_object* v_x_306_, lean_object* v_x_307_, lean_object* v_x_308_, lean_object* v_x_309_){
_start:
{
size_t v_x_2437__boxed_310_; lean_object* v_res_311_; 
v_x_2437__boxed_310_ = lean_unbox_usize(v_x_307_);
lean_dec(v_x_307_);
v_res_311_ = l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0(v_00_u03b2_305_, v_x_306_, v_x_2437__boxed_310_, v_x_308_, v_x_309_);
lean_dec_ref(v_x_309_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1(lean_object* v_00_u03b2_312_, lean_object* v_x_313_, lean_object* v_x_314_, lean_object* v_x_315_){
_start:
{
lean_object* v___x_316_; 
v___x_316_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1___redArg(v_x_313_, v_x_314_, v_x_315_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0(lean_object* v_00_u03b2_317_, lean_object* v_keys_318_, lean_object* v_vals_319_, lean_object* v_heq_320_, lean_object* v_i_321_, lean_object* v_k_322_, lean_object* v_k_u2080_323_){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0___redArg(v_keys_318_, v_i_321_, v_k_322_, v_k_u2080_323_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0___boxed(lean_object* v_00_u03b2_325_, lean_object* v_keys_326_, lean_object* v_vals_327_, lean_object* v_heq_328_, lean_object* v_i_329_, lean_object* v_k_330_, lean_object* v_k_u2080_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0(v_00_u03b2_325_, v_keys_326_, v_vals_327_, v_heq_328_, v_i_329_, v_k_330_, v_k_u2080_331_);
lean_dec_ref(v_k_u2080_331_);
lean_dec_ref(v_vals_327_);
lean_dec_ref(v_keys_326_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2(lean_object* v_00_u03b2_333_, lean_object* v_x_334_, size_t v_x_335_, size_t v_x_336_, lean_object* v_x_337_, lean_object* v_x_338_){
_start:
{
lean_object* v___x_339_; 
v___x_339_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg(v_x_334_, v_x_335_, v_x_336_, v_x_337_, v_x_338_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_340_, lean_object* v_x_341_, lean_object* v_x_342_, lean_object* v_x_343_, lean_object* v_x_344_, lean_object* v_x_345_){
_start:
{
size_t v_x_2461__boxed_346_; size_t v_x_2462__boxed_347_; lean_object* v_res_348_; 
v_x_2461__boxed_346_ = lean_unbox_usize(v_x_342_);
lean_dec(v_x_342_);
v_x_2462__boxed_347_ = lean_unbox_usize(v_x_343_);
lean_dec(v_x_343_);
v_res_348_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2(v_00_u03b2_340_, v_x_341_, v_x_2461__boxed_346_, v_x_2462__boxed_347_, v_x_344_, v_x_345_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_349_, lean_object* v_n_350_, lean_object* v_k_351_, lean_object* v_v_352_){
_start:
{
lean_object* v___x_353_; 
v___x_353_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__3___redArg(v_n_350_, v_k_351_, v_v_352_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_354_, size_t v_depth_355_, lean_object* v_keys_356_, lean_object* v_vals_357_, lean_object* v_heq_358_, lean_object* v_i_359_, lean_object* v_entries_360_){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4___redArg(v_depth_355_, v_keys_356_, v_vals_357_, v_i_359_, v_entries_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_362_, lean_object* v_depth_363_, lean_object* v_keys_364_, lean_object* v_vals_365_, lean_object* v_heq_366_, lean_object* v_i_367_, lean_object* v_entries_368_){
_start:
{
size_t v_depth_boxed_369_; lean_object* v_res_370_; 
v_depth_boxed_369_ = lean_unbox_usize(v_depth_363_);
lean_dec(v_depth_363_);
v_res_370_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4(v_00_u03b2_362_, v_depth_boxed_369_, v_keys_364_, v_vals_365_, v_heq_366_, v_i_367_, v_entries_368_);
lean_dec_ref(v_vals_365_);
lean_dec_ref(v_keys_364_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_371_, lean_object* v_x_372_, lean_object* v_x_373_, lean_object* v_x_374_, lean_object* v_x_375_){
_start:
{
lean_object* v___x_376_; 
v___x_376_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__3_spec__4___redArg(v_x_372_, v_x_373_, v_x_374_, v_x_375_);
return v___x_376_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0(void){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = l_Lean_Meta_Sym_instInhabitedSymM(lean_box(0));
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0(lean_object* v_msg_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_){
_start:
{
lean_object* v___x_386_; lean_object* v___x_756__overap_387_; lean_object* v___x_388_; 
v___x_386_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0, &l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0);
v___x_756__overap_387_ = lean_panic_fn_borrowed(v___x_386_, v_msg_378_);
lean_inc(v___y_384_);
lean_inc_ref(v___y_383_);
lean_inc(v___y_382_);
lean_inc_ref(v___y_381_);
lean_inc(v___y_380_);
lean_inc_ref(v___y_379_);
v___x_388_ = lean_apply_7(v___x_756__overap_387_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, lean_box(0));
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___boxed(lean_object* v_msg_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0(v_msg_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_);
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
lean_dec(v___y_391_);
lean_dec_ref(v___y_390_);
return v_res_397_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__3(void){
_start:
{
lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_401_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__2));
v___x_402_ = lean_unsigned_to_nat(2u);
v___x_403_ = lean_unsigned_to_nat(42u);
v___x_404_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__1));
v___x_405_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_406_ = l_mkPanicMessageWithDecl(v___x_405_, v___x_404_, v___x_403_, v___x_402_, v___x_401_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object* v_e_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_){
_start:
{
lean_object* v___x_415_; lean_object* v_share_416_; lean_object* v___x_417_; uint64_t v___x_418_; size_t v___x_419_; lean_object* v___x_420_; uint8_t v___x_421_; 
v___x_415_ = lean_st_ref_get(v_a_409_);
v_share_416_ = lean_ctor_get(v___x_415_, 0);
lean_inc_ref(v_share_416_);
lean_dec(v___x_415_);
v___x_417_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy;
v___x_418_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_407_);
v___x_419_ = lean_uint64_to_usize(v___x_418_);
lean_inc_ref(v_e_407_);
v___x_420_ = l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg(v_share_416_, v___x_419_, v_e_407_, v___x_417_);
v___x_421_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_420_, v_e_407_);
lean_dec_ref(v_e_407_);
lean_dec_ref(v___x_420_);
if (v___x_421_ == 0)
{
lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_422_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__3, &l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__3_once, _init_l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__3);
v___x_423_ = l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0(v___x_422_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_);
return v___x_423_;
}
else
{
lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_424_ = lean_box(0);
v___x_425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_425_, 0, v___x_424_);
return v___x_425_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared___boxed(lean_object* v_e_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_e_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_);
lean_dec(v_a_432_);
lean_dec_ref(v_a_431_);
lean_dec(v_a_430_);
lean_dec_ref(v_a_429_);
lean_dec(v_a_428_);
lean_dec_ref(v_a_427_);
return v_res_434_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__0(void){
_start:
{
lean_object* v___x_443_; 
v___x_443_ = l_Lean_Meta_Sym_instInhabitedSymM(lean_box(0));
return v___x_443_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__3(void){
_start:
{
lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_446_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2));
v___x_447_ = lean_unsigned_to_nat(16u);
v___x_448_ = lean_unsigned_to_nat(62u);
v___x_449_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__1));
v___x_450_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_451_ = l_mkPanicMessageWithDecl(v___x_450_, v___x_449_, v___x_448_, v___x_447_, v___x_446_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM___redArg(lean_object* v_k_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_){
_start:
{
lean_object* v___x_460_; lean_object* v___x_461_; uint8_t v_debug_462_; lean_object* v_env_463_; lean_object* v___x_464_; lean_object* v___x_465_; uint8_t v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_460_ = lean_st_ref_get(v_a_454_);
v___x_461_ = lean_st_ref_get(v_a_458_);
v_debug_462_ = lean_ctor_get_uint8(v___x_460_, sizeof(void*)*11);
lean_dec(v___x_460_);
v_env_463_ = lean_ctor_get(v___x_461_, 0);
lean_inc_ref(v_env_463_);
lean_dec(v___x_461_);
v___x_464_ = lean_box(v_debug_462_);
v___x_465_ = lean_apply_1(v_k_452_, v___x_464_);
v___x_466_ = 0;
v___x_467_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_467_, 0, v_env_463_);
lean_ctor_set_uint8(v___x_467_, sizeof(void*)*1, v___x_466_);
lean_ctor_set_uint8(v___x_467_, sizeof(void*)*1 + 1, v___x_466_);
v___x_468_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___x_465_, v___x_467_, v_a_454_);
if (lean_obj_tag(v___x_468_) == 0)
{
lean_object* v_a_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_481_; 
v_a_469_ = lean_ctor_get(v___x_468_, 0);
v_isSharedCheck_481_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_481_ == 0)
{
v___x_471_ = v___x_468_;
v_isShared_472_ = v_isSharedCheck_481_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_a_469_);
lean_dec(v___x_468_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_481_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
if (lean_obj_tag(v_a_469_) == 0)
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_1305__overap_475_; lean_object* v___x_476_; 
lean_dec_ref_known(v_a_469_, 1);
lean_del_object(v___x_471_);
v___x_473_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__0, &l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__0_once, _init_l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__0);
v___x_474_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__3, &l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__3_once, _init_l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__3);
v___x_1305__overap_475_ = l_panic___redArg(v___x_473_, v___x_474_);
lean_inc(v_a_458_);
lean_inc_ref(v_a_457_);
lean_inc(v_a_456_);
lean_inc_ref(v_a_455_);
lean_inc(v_a_454_);
lean_inc_ref(v_a_453_);
v___x_476_ = lean_apply_7(v___x_1305__overap_475_, v_a_453_, v_a_454_, v_a_455_, v_a_456_, v_a_457_, v_a_458_, lean_box(0));
return v___x_476_;
}
else
{
lean_object* v_a_477_; lean_object* v___x_479_; 
v_a_477_ = lean_ctor_get(v_a_469_, 0);
lean_inc(v_a_477_);
lean_dec_ref_known(v_a_469_, 1);
if (v_isShared_472_ == 0)
{
lean_ctor_set(v___x_471_, 0, v_a_477_);
v___x_479_ = v___x_471_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_a_477_);
v___x_479_ = v_reuseFailAlloc_480_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
return v___x_479_;
}
}
}
}
else
{
lean_object* v_a_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_489_; 
v_a_482_ = lean_ctor_get(v___x_468_, 0);
v_isSharedCheck_489_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_489_ == 0)
{
v___x_484_ = v___x_468_;
v_isShared_485_ = v_isSharedCheck_489_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_a_482_);
lean_dec(v___x_468_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_489_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v___x_487_; 
if (v_isShared_485_ == 0)
{
v___x_487_ = v___x_484_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v_a_482_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
return v___x_487_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___boxed(lean_object* v_k_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_Lean_Meta_Sym_Internal_liftBuilderM___redArg(v_k_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_, v_a_495_, v_a_496_);
lean_dec(v_a_496_);
lean_dec_ref(v_a_495_);
lean_dec(v_a_494_);
lean_dec_ref(v_a_493_);
lean_dec(v_a_492_);
lean_dec_ref(v_a_491_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM(lean_object* v_00_u03b1_499_, lean_object* v_k_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_){
_start:
{
lean_object* v___x_508_; lean_object* v___x_509_; uint8_t v_debug_510_; lean_object* v_env_511_; lean_object* v___x_512_; lean_object* v___x_513_; uint8_t v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_508_ = lean_st_ref_get(v_a_502_);
v___x_509_ = lean_st_ref_get(v_a_506_);
v_debug_510_ = lean_ctor_get_uint8(v___x_508_, sizeof(void*)*11);
lean_dec(v___x_508_);
v_env_511_ = lean_ctor_get(v___x_509_, 0);
lean_inc_ref(v_env_511_);
lean_dec(v___x_509_);
v___x_512_ = lean_box(v_debug_510_);
v___x_513_ = lean_apply_1(v_k_500_, v___x_512_);
v___x_514_ = 0;
v___x_515_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_515_, 0, v_env_511_);
lean_ctor_set_uint8(v___x_515_, sizeof(void*)*1, v___x_514_);
lean_ctor_set_uint8(v___x_515_, sizeof(void*)*1 + 1, v___x_514_);
v___x_516_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___x_513_, v___x_515_, v_a_502_);
if (lean_obj_tag(v___x_516_) == 0)
{
lean_object* v_a_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_529_; 
v_a_517_ = lean_ctor_get(v___x_516_, 0);
v_isSharedCheck_529_ = !lean_is_exclusive(v___x_516_);
if (v_isSharedCheck_529_ == 0)
{
v___x_519_ = v___x_516_;
v_isShared_520_ = v_isSharedCheck_529_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_a_517_);
lean_dec(v___x_516_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_529_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
if (lean_obj_tag(v_a_517_) == 0)
{
lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_1333__overap_523_; lean_object* v___x_524_; 
lean_dec_ref_known(v_a_517_, 1);
lean_del_object(v___x_519_);
v___x_521_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__0, &l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__0_once, _init_l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__0);
v___x_522_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__3, &l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__3_once, _init_l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__3);
v___x_1333__overap_523_ = l_panic___redArg(v___x_521_, v___x_522_);
lean_inc(v_a_506_);
lean_inc_ref(v_a_505_);
lean_inc(v_a_504_);
lean_inc_ref(v_a_503_);
lean_inc(v_a_502_);
lean_inc_ref(v_a_501_);
v___x_524_ = lean_apply_7(v___x_1333__overap_523_, v_a_501_, v_a_502_, v_a_503_, v_a_504_, v_a_505_, v_a_506_, lean_box(0));
return v___x_524_;
}
else
{
lean_object* v_a_525_; lean_object* v___x_527_; 
v_a_525_ = lean_ctor_get(v_a_517_, 0);
lean_inc(v_a_525_);
lean_dec_ref_known(v_a_517_, 1);
if (v_isShared_520_ == 0)
{
lean_ctor_set(v___x_519_, 0, v_a_525_);
v___x_527_ = v___x_519_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v_a_525_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
return v___x_527_;
}
}
}
}
else
{
lean_object* v_a_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_537_; 
v_a_530_ = lean_ctor_get(v___x_516_, 0);
v_isSharedCheck_537_ = !lean_is_exclusive(v___x_516_);
if (v_isSharedCheck_537_ == 0)
{
v___x_532_ = v___x_516_;
v_isShared_533_ = v_isSharedCheck_537_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_a_530_);
lean_dec(v___x_516_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_537_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___x_535_; 
if (v_isShared_533_ == 0)
{
v___x_535_ = v___x_532_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v_a_530_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
return v___x_535_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM___boxed(lean_object* v_00_u03b1_538_, lean_object* v_k_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_Lean_Meta_Sym_Internal_liftBuilderM(v_00_u03b1_538_, v_k_539_, v_a_540_, v_a_541_, v_a_542_, v_a_543_, v_a_544_, v_a_545_);
lean_dec(v_a_545_);
lean_dec_ref(v_a_544_);
lean_dec(v_a_543_);
lean_dec_ref(v_a_542_);
lean_dec(v_a_541_);
lean_dec_ref(v_a_540_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_share1___redArg(lean_object* v_e_548_, lean_object* v_a_549_){
_start:
{
lean_object* v___x_550_; uint64_t v___x_551_; size_t v___x_552_; lean_object* v___x_553_; uint8_t v___x_554_; 
v___x_550_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy;
v___x_551_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_548_);
v___x_552_ = lean_uint64_to_usize(v___x_551_);
lean_inc_ref(v_e_548_);
lean_inc_ref(v_a_549_);
v___x_553_ = l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg(v_a_549_, v___x_552_, v_e_548_, v___x_550_);
v___x_554_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_553_, v___x_550_);
if (v___x_554_ == 0)
{
lean_object* v___x_555_; 
lean_dec_ref(v_e_548_);
v___x_555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_555_, 0, v___x_553_);
lean_ctor_set(v___x_555_, 1, v_a_549_);
return v___x_555_;
}
else
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
lean_dec_ref(v___x_553_);
v___x_556_ = lean_box(0);
lean_inc_ref(v_e_548_);
v___x_557_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1___redArg(v_a_549_, v_e_548_, v___x_556_);
v___x_558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_558_, 0, v_e_548_);
lean_ctor_set(v___x_558_, 1, v___x_557_);
return v___x_558_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_share1(lean_object* v_e_559_, uint8_t v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_){
_start:
{
lean_object* v___x_563_; 
v___x_563_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v_e_559_, v_a_562_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_share1___boxed(lean_object* v_e_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_){
_start:
{
uint8_t v_a_boxed_568_; lean_object* v_res_569_; 
v_a_boxed_568_ = lean_unbox(v_a_565_);
v_res_569_ = l_Lean_Meta_Sym_Internal_Builder_share1(v_e_564_, v_a_boxed_568_, v_a_566_, v_a_567_);
lean_dec_ref(v_a_566_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1(lean_object* v_msg_572_, uint8_t v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_){
_start:
{
lean_object* v___f_576_; lean_object* v___f_577_; lean_object* v___x_578_; lean_object* v___f_579_; lean_object* v___f_580_; lean_object* v___f_581_; lean_object* v___x_696__overap_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v___f_576_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__0));
v___f_577_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__1));
v___x_578_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___f_576_, v___f_577_);
v___f_579_ = lean_alloc_closure((void*)(l_EStateM_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_579_, 0, v___x_578_);
v___f_580_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_580_, 0, v___f_579_);
v___f_581_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_581_, 0, v___f_580_);
v___x_696__overap_582_ = lean_panic_fn_borrowed(v___f_581_, v_msg_572_);
lean_dec_ref(v___f_581_);
v___x_583_ = lean_box(v___y_573_);
lean_inc_ref(v___y_574_);
v___x_584_ = lean_apply_3(v___x_696__overap_582_, v___x_583_, v___y_574_, v___y_575_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___boxed(lean_object* v_msg_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_){
_start:
{
uint8_t v___y_798__boxed_589_; lean_object* v_res_590_; 
v___y_798__boxed_589_ = lean_unbox(v___y_586_);
v_res_590_ = l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1(v_msg_585_, v___y_798__boxed_589_, v___y_587_, v___y_588_);
lean_dec_ref(v___y_587_);
return v_res_590_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_591_, lean_object* v_i_592_, lean_object* v_k_593_){
_start:
{
lean_object* v___x_594_; uint8_t v___x_595_; 
v___x_594_ = lean_array_get_size(v_keys_591_);
v___x_595_ = lean_nat_dec_lt(v_i_592_, v___x_594_);
if (v___x_595_ == 0)
{
lean_dec_ref(v_k_593_);
lean_dec(v_i_592_);
return v___x_595_;
}
else
{
lean_object* v_k_x27_596_; uint8_t v___x_597_; 
v_k_x27_596_ = lean_array_fget_borrowed(v_keys_591_, v_i_592_);
lean_inc(v_k_x27_596_);
lean_inc_ref(v_k_593_);
v___x_597_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_k_593_, v_k_x27_596_);
if (v___x_597_ == 0)
{
lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_598_ = lean_unsigned_to_nat(1u);
v___x_599_ = lean_nat_add(v_i_592_, v___x_598_);
lean_dec(v_i_592_);
v_i_592_ = v___x_599_;
goto _start;
}
else
{
lean_dec_ref(v_k_593_);
lean_dec(v_i_592_);
return v___x_597_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_601_, lean_object* v_i_602_, lean_object* v_k_603_){
_start:
{
uint8_t v_res_604_; lean_object* v_r_605_; 
v_res_604_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg(v_keys_601_, v_i_602_, v_k_603_);
lean_dec_ref(v_keys_601_);
v_r_605_ = lean_box(v_res_604_);
return v_r_605_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg(lean_object* v_x_606_, size_t v_x_607_, lean_object* v_x_608_){
_start:
{
if (lean_obj_tag(v_x_606_) == 0)
{
lean_object* v_es_609_; lean_object* v___x_610_; size_t v___x_611_; size_t v___x_612_; lean_object* v_j_613_; lean_object* v___x_614_; 
v_es_609_ = lean_ctor_get(v_x_606_, 0);
lean_inc_ref(v_es_609_);
lean_dec_ref_known(v_x_606_, 1);
v___x_610_ = lean_box(2);
v___x_611_ = ((size_t)31ULL);
v___x_612_ = lean_usize_land(v_x_607_, v___x_611_);
v_j_613_ = lean_usize_to_nat(v___x_612_);
v___x_614_ = lean_array_get(v___x_610_, v_es_609_, v_j_613_);
lean_dec(v_j_613_);
lean_dec_ref(v_es_609_);
switch(lean_obj_tag(v___x_614_))
{
case 0:
{
lean_object* v_key_615_; uint8_t v___x_616_; 
v_key_615_ = lean_ctor_get(v___x_614_, 0);
lean_inc(v_key_615_);
lean_dec_ref_known(v___x_614_, 2);
v___x_616_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_608_, v_key_615_);
return v___x_616_;
}
case 1:
{
lean_object* v_node_617_; size_t v___x_618_; size_t v___x_619_; 
v_node_617_ = lean_ctor_get(v___x_614_, 0);
lean_inc(v_node_617_);
lean_dec_ref_known(v___x_614_, 1);
v___x_618_ = ((size_t)5ULL);
v___x_619_ = lean_usize_shift_right(v_x_607_, v___x_618_);
v_x_606_ = v_node_617_;
v_x_607_ = v___x_619_;
goto _start;
}
default: 
{
uint8_t v___x_621_; 
lean_dec_ref(v_x_608_);
v___x_621_ = 0;
return v___x_621_;
}
}
}
else
{
lean_object* v_ks_622_; lean_object* v___x_623_; uint8_t v___x_624_; 
v_ks_622_ = lean_ctor_get(v_x_606_, 0);
lean_inc_ref(v_ks_622_);
lean_dec_ref_known(v_x_606_, 2);
v___x_623_ = lean_unsigned_to_nat(0u);
v___x_624_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg(v_ks_622_, v___x_623_, v_x_608_);
lean_dec_ref(v_ks_622_);
return v___x_624_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg___boxed(lean_object* v_x_625_, lean_object* v_x_626_, lean_object* v_x_627_){
_start:
{
size_t v_x_838__boxed_628_; uint8_t v_res_629_; lean_object* v_r_630_; 
v_x_838__boxed_628_ = lean_unbox_usize(v_x_626_);
lean_dec(v_x_626_);
v_res_629_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg(v_x_625_, v_x_838__boxed_628_, v_x_627_);
v_r_630_ = lean_box(v_res_629_);
return v_r_630_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg(lean_object* v_x_631_, lean_object* v_x_632_){
_start:
{
uint64_t v___x_633_; size_t v___x_634_; uint8_t v___x_635_; 
v___x_633_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_632_);
v___x_634_ = lean_uint64_to_usize(v___x_633_);
v___x_635_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg(v_x_631_, v___x_634_, v_x_632_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg___boxed(lean_object* v_x_636_, lean_object* v_x_637_){
_start:
{
uint8_t v_res_638_; lean_object* v_r_639_; 
v_res_638_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg(v_x_636_, v_x_637_);
v_r_639_ = lean_box(v_res_638_);
return v_r_639_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__2(void){
_start:
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_642_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__1));
v___x_643_ = lean_unsigned_to_nat(2u);
v___x_644_ = lean_unsigned_to_nat(74u);
v___x_645_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__0));
v___x_646_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_647_ = l_mkPanicMessageWithDecl(v___x_646_, v___x_645_, v___x_644_, v___x_643_, v___x_642_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_assertShared(lean_object* v_e_648_, uint8_t v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_){
_start:
{
uint8_t v___x_652_; 
lean_inc_ref(v_a_651_);
v___x_652_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg(v_a_651_, v_e_648_);
if (v___x_652_ == 0)
{
lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_653_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__2, &l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__2_once, _init_l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__2);
v___x_654_ = l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1(v___x_653_, v_a_649_, v_a_650_, v_a_651_);
return v___x_654_;
}
else
{
lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_655_ = lean_box(0);
v___x_656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_656_, 0, v___x_655_);
lean_ctor_set(v___x_656_, 1, v_a_651_);
return v___x_656_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_assertShared___boxed(lean_object* v_e_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_){
_start:
{
uint8_t v_a_boxed_661_; lean_object* v_res_662_; 
v_a_boxed_661_ = lean_unbox(v_a_658_);
v_res_662_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_e_657_, v_a_boxed_661_, v_a_659_, v_a_660_);
lean_dec_ref(v_a_659_);
return v_res_662_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0(lean_object* v_00_u03b2_663_, lean_object* v_x_664_, lean_object* v_x_665_){
_start:
{
uint8_t v___x_666_; 
v___x_666_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg(v_x_664_, v_x_665_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___boxed(lean_object* v_00_u03b2_667_, lean_object* v_x_668_, lean_object* v_x_669_){
_start:
{
uint8_t v_res_670_; lean_object* v_r_671_; 
v_res_670_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0(v_00_u03b2_667_, v_x_668_, v_x_669_);
v_r_671_ = lean_box(v_res_670_);
return v_r_671_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0(lean_object* v_00_u03b2_672_, lean_object* v_x_673_, size_t v_x_674_, lean_object* v_x_675_){
_start:
{
uint8_t v___x_676_; 
v___x_676_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg(v_x_673_, v_x_674_, v_x_675_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___boxed(lean_object* v_00_u03b2_677_, lean_object* v_x_678_, lean_object* v_x_679_, lean_object* v_x_680_){
_start:
{
size_t v_x_937__boxed_681_; uint8_t v_res_682_; lean_object* v_r_683_; 
v_x_937__boxed_681_ = lean_unbox_usize(v_x_679_);
lean_dec(v_x_679_);
v_res_682_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0(v_00_u03b2_677_, v_x_678_, v_x_937__boxed_681_, v_x_680_);
v_r_683_ = lean_box(v_res_682_);
return v_r_683_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_684_, lean_object* v_keys_685_, lean_object* v_vals_686_, lean_object* v_heq_687_, lean_object* v_i_688_, lean_object* v_k_689_){
_start:
{
uint8_t v___x_690_; 
v___x_690_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg(v_keys_685_, v_i_688_, v_k_689_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_691_, lean_object* v_keys_692_, lean_object* v_vals_693_, lean_object* v_heq_694_, lean_object* v_i_695_, lean_object* v_k_696_){
_start:
{
uint8_t v_res_697_; lean_object* v_r_698_; 
v_res_697_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2(v_00_u03b2_691_, v_keys_692_, v_vals_693_, v_heq_694_, v_i_695_, v_k_696_);
lean_dec_ref(v_vals_693_);
lean_dec_ref(v_keys_692_);
v_r_698_ = lean_box(v_res_697_);
return v_r_698_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__10(void){
_start:
{
lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_718_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__9));
v___x_719_ = l_ReaderT_instMonad___redArg(v___x_718_);
return v___x_719_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__13(void){
_start:
{
lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_722_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__10, &l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__10_once, _init_l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__10);
v___x_723_ = lean_alloc_closure((void*)(l_ReaderT_read___boxed), 4, 3);
lean_closure_set(v___x_723_, 0, lean_box(0));
lean_closure_set(v___x_723_, 1, lean_box(0));
lean_closure_set(v___x_723_, 2, v___x_722_);
return v___x_723_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__14(void){
_start:
{
lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_724_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__13, &l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__13_once, _init_l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__13);
v___x_725_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__12));
v___x_726_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__11));
v___x_727_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_727_, 0, v___x_726_);
lean_ctor_set(v___x_727_, 1, v___x_725_);
lean_ctor_set(v___x_727_, 2, v___x_724_);
return v___x_727_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM(void){
_start:
{
lean_object* v___x_728_; 
v___x_728_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__14, &l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__14_once, _init_l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__14);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLitS___redArg(lean_object* v_inst_729_, lean_object* v_l_730_){
_start:
{
lean_object* v_share1_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
v_share1_731_ = lean_ctor_get(v_inst_729_, 0);
lean_inc(v_share1_731_);
lean_dec_ref(v_inst_729_);
v___x_732_ = l_Lean_Expr_lit___override(v_l_730_);
v___x_733_ = lean_apply_1(v_share1_731_, v___x_732_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLitS(lean_object* v_m_734_, lean_object* v_inst_735_, lean_object* v_l_736_){
_start:
{
lean_object* v___x_737_; 
v___x_737_ = l_Lean_Meta_Sym_Internal_mkLitS___redArg(v_inst_735_, v_l_736_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___redArg(lean_object* v_inst_738_, lean_object* v_declName_739_, lean_object* v_us_740_){
_start:
{
lean_object* v_share1_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v_share1_741_ = lean_ctor_get(v_inst_738_, 0);
lean_inc(v_share1_741_);
lean_dec_ref(v_inst_738_);
v___x_742_ = l_Lean_Expr_const___override(v_declName_739_, v_us_740_);
v___x_743_ = lean_apply_1(v_share1_741_, v___x_742_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS(lean_object* v_m_744_, lean_object* v_inst_745_, lean_object* v_declName_746_, lean_object* v_us_747_){
_start:
{
lean_object* v___x_748_; 
v___x_748_ = l_Lean_Meta_Sym_Internal_mkConstS___redArg(v_inst_745_, v_declName_746_, v_us_747_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___redArg(lean_object* v_inst_749_, lean_object* v_idx_750_){
_start:
{
lean_object* v_share1_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
v_share1_751_ = lean_ctor_get(v_inst_749_, 0);
lean_inc(v_share1_751_);
lean_dec_ref(v_inst_749_);
v___x_752_ = l_Lean_Expr_bvar___override(v_idx_750_);
v___x_753_ = lean_apply_1(v_share1_751_, v___x_752_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS(lean_object* v_m_754_, lean_object* v_inst_755_, lean_object* v_idx_756_){
_start:
{
lean_object* v___x_757_; 
v___x_757_ = l_Lean_Meta_Sym_Internal_mkBVarS___redArg(v_inst_755_, v_idx_756_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS___redArg(lean_object* v_inst_758_, lean_object* v_u_759_){
_start:
{
lean_object* v_share1_760_; lean_object* v___x_761_; lean_object* v___x_762_; 
v_share1_760_ = lean_ctor_get(v_inst_758_, 0);
lean_inc(v_share1_760_);
lean_dec_ref(v_inst_758_);
v___x_761_ = l_Lean_Expr_sort___override(v_u_759_);
v___x_762_ = lean_apply_1(v_share1_760_, v___x_761_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS(lean_object* v_m_763_, lean_object* v_inst_764_, lean_object* v_u_765_){
_start:
{
lean_object* v___x_766_; 
v___x_766_ = l_Lean_Meta_Sym_Internal_mkSortS___redArg(v_inst_764_, v_u_765_);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___redArg(lean_object* v_inst_767_, lean_object* v_fvarId_768_){
_start:
{
lean_object* v_share1_769_; lean_object* v___x_770_; lean_object* v___x_771_; 
v_share1_769_ = lean_ctor_get(v_inst_767_, 0);
lean_inc(v_share1_769_);
lean_dec_ref(v_inst_767_);
v___x_770_ = l_Lean_Expr_fvar___override(v_fvarId_768_);
v___x_771_ = lean_apply_1(v_share1_769_, v___x_770_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS(lean_object* v_m_772_, lean_object* v_inst_773_, lean_object* v_fvarId_774_){
_start:
{
lean_object* v___x_775_; 
v___x_775_ = l_Lean_Meta_Sym_Internal_mkFVarS___redArg(v_inst_773_, v_fvarId_774_);
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMVarS___redArg(lean_object* v_inst_776_, lean_object* v_mvarId_777_){
_start:
{
lean_object* v_share1_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
v_share1_778_ = lean_ctor_get(v_inst_776_, 0);
lean_inc(v_share1_778_);
lean_dec_ref(v_inst_776_);
v___x_779_ = l_Lean_Expr_mvar___override(v_mvarId_777_);
v___x_780_ = lean_apply_1(v_share1_778_, v___x_779_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMVarS(lean_object* v_m_781_, lean_object* v_inst_782_, lean_object* v_mvarId_783_){
_start:
{
lean_object* v___x_784_; 
v___x_784_ = l_Lean_Meta_Sym_Internal_mkMVarS___redArg(v_inst_782_, v_mvarId_783_);
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__0(lean_object* v_d_785_, lean_object* v_e_786_, lean_object* v_share1_787_, lean_object* v_____r_788_){
_start:
{
lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_789_ = l_Lean_Expr_mdata___override(v_d_785_, v_e_786_);
v___x_790_ = lean_apply_1(v_share1_787_, v___x_789_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1(lean_object* v___f_791_, lean_object* v_____r_792_){
_start:
{
lean_object* v___x_793_; 
v___x_793_ = lean_apply_1(v___f_791_, v_____r_792_);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__2(lean_object* v___f_794_, lean_object* v_assertShared_795_, lean_object* v_e_796_, lean_object* v_toBind_797_, lean_object* v___f_798_, uint8_t v_____do__lift_799_){
_start:
{
if (v_____do__lift_799_ == 0)
{
lean_object* v___x_800_; lean_object* v___x_801_; 
lean_dec(v___f_798_);
lean_dec(v_toBind_797_);
lean_dec_ref(v_e_796_);
lean_dec(v_assertShared_795_);
v___x_800_ = lean_box(0);
v___x_801_ = lean_apply_1(v___f_794_, v___x_800_);
return v___x_801_;
}
else
{
lean_object* v___x_802_; lean_object* v___x_803_; 
lean_dec(v___f_794_);
v___x_802_ = lean_apply_1(v_assertShared_795_, v_e_796_);
v___x_803_ = lean_apply_4(v_toBind_797_, lean_box(0), lean_box(0), v___x_802_, v___f_798_);
return v___x_803_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__2___boxed(lean_object* v___f_804_, lean_object* v_assertShared_805_, lean_object* v_e_806_, lean_object* v_toBind_807_, lean_object* v___f_808_, lean_object* v_____do__lift_809_){
_start:
{
uint8_t v_____do__lift_86__boxed_810_; lean_object* v_res_811_; 
v_____do__lift_86__boxed_810_ = lean_unbox(v_____do__lift_809_);
v_res_811_ = l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__2(v___f_804_, v_assertShared_805_, v_e_806_, v_toBind_807_, v___f_808_, v_____do__lift_86__boxed_810_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg(lean_object* v_inst_812_, lean_object* v_inst_813_, lean_object* v_d_814_, lean_object* v_e_815_){
_start:
{
lean_object* v_toBind_816_; lean_object* v_share1_817_; lean_object* v_assertShared_818_; lean_object* v_isDebugEnabled_819_; lean_object* v___f_820_; lean_object* v___f_821_; lean_object* v___f_822_; lean_object* v___x_823_; 
v_toBind_816_ = lean_ctor_get(v_inst_813_, 1);
lean_inc_n(v_toBind_816_, 2);
lean_dec_ref(v_inst_813_);
v_share1_817_ = lean_ctor_get(v_inst_812_, 0);
lean_inc(v_share1_817_);
v_assertShared_818_ = lean_ctor_get(v_inst_812_, 1);
lean_inc(v_assertShared_818_);
v_isDebugEnabled_819_ = lean_ctor_get(v_inst_812_, 2);
lean_inc(v_isDebugEnabled_819_);
lean_dec_ref(v_inst_812_);
lean_inc_ref(v_e_815_);
v___f_820_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__0), 4, 3);
lean_closure_set(v___f_820_, 0, v_d_814_);
lean_closure_set(v___f_820_, 1, v_e_815_);
lean_closure_set(v___f_820_, 2, v_share1_817_);
lean_inc_ref(v___f_820_);
v___f_821_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_821_, 0, v___f_820_);
v___f_822_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_822_, 0, v___f_820_);
lean_closure_set(v___f_822_, 1, v_assertShared_818_);
lean_closure_set(v___f_822_, 2, v_e_815_);
lean_closure_set(v___f_822_, 3, v_toBind_816_);
lean_closure_set(v___f_822_, 4, v___f_821_);
v___x_823_ = lean_apply_4(v_toBind_816_, lean_box(0), lean_box(0), v_isDebugEnabled_819_, v___f_822_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS(lean_object* v_m_824_, lean_object* v_inst_825_, lean_object* v_inst_826_, lean_object* v_d_827_, lean_object* v_e_828_){
_start:
{
lean_object* v___x_829_; 
v___x_829_ = l_Lean_Meta_Sym_Internal_mkMDataS___redArg(v_inst_825_, v_inst_826_, v_d_827_, v_e_828_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__0(lean_object* v_structName_830_, lean_object* v_idx_831_, lean_object* v_struct_832_, lean_object* v_share1_833_, lean_object* v_____r_834_){
_start:
{
lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_835_ = l_Lean_Expr_proj___override(v_structName_830_, v_idx_831_, v_struct_832_);
v___x_836_ = lean_apply_1(v_share1_833_, v___x_835_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__2(lean_object* v___f_837_, lean_object* v_assertShared_838_, lean_object* v_struct_839_, lean_object* v_toBind_840_, lean_object* v___f_841_, uint8_t v_____do__lift_842_){
_start:
{
if (v_____do__lift_842_ == 0)
{
lean_object* v___x_843_; lean_object* v___x_844_; 
lean_dec(v___f_841_);
lean_dec(v_toBind_840_);
lean_dec_ref(v_struct_839_);
lean_dec(v_assertShared_838_);
v___x_843_ = lean_box(0);
v___x_844_ = lean_apply_1(v___f_837_, v___x_843_);
return v___x_844_;
}
else
{
lean_object* v___x_845_; lean_object* v___x_846_; 
lean_dec(v___f_837_);
v___x_845_ = lean_apply_1(v_assertShared_838_, v_struct_839_);
v___x_846_ = lean_apply_4(v_toBind_840_, lean_box(0), lean_box(0), v___x_845_, v___f_841_);
return v___x_846_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__2___boxed(lean_object* v___f_847_, lean_object* v_assertShared_848_, lean_object* v_struct_849_, lean_object* v_toBind_850_, lean_object* v___f_851_, lean_object* v_____do__lift_852_){
_start:
{
uint8_t v_____do__lift_80__boxed_853_; lean_object* v_res_854_; 
v_____do__lift_80__boxed_853_ = lean_unbox(v_____do__lift_852_);
v_res_854_ = l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__2(v___f_847_, v_assertShared_848_, v_struct_849_, v_toBind_850_, v___f_851_, v_____do__lift_80__boxed_853_);
return v_res_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___redArg(lean_object* v_inst_855_, lean_object* v_inst_856_, lean_object* v_structName_857_, lean_object* v_idx_858_, lean_object* v_struct_859_){
_start:
{
lean_object* v_toBind_860_; lean_object* v_share1_861_; lean_object* v_assertShared_862_; lean_object* v_isDebugEnabled_863_; lean_object* v___f_864_; lean_object* v___f_865_; lean_object* v___f_866_; lean_object* v___x_867_; 
v_toBind_860_ = lean_ctor_get(v_inst_856_, 1);
lean_inc_n(v_toBind_860_, 2);
lean_dec_ref(v_inst_856_);
v_share1_861_ = lean_ctor_get(v_inst_855_, 0);
lean_inc(v_share1_861_);
v_assertShared_862_ = lean_ctor_get(v_inst_855_, 1);
lean_inc(v_assertShared_862_);
v_isDebugEnabled_863_ = lean_ctor_get(v_inst_855_, 2);
lean_inc(v_isDebugEnabled_863_);
lean_dec_ref(v_inst_855_);
lean_inc_ref(v_struct_859_);
v___f_864_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__0), 5, 4);
lean_closure_set(v___f_864_, 0, v_structName_857_);
lean_closure_set(v___f_864_, 1, v_idx_858_);
lean_closure_set(v___f_864_, 2, v_struct_859_);
lean_closure_set(v___f_864_, 3, v_share1_861_);
lean_inc_ref(v___f_864_);
v___f_865_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_865_, 0, v___f_864_);
v___f_866_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_866_, 0, v___f_864_);
lean_closure_set(v___f_866_, 1, v_assertShared_862_);
lean_closure_set(v___f_866_, 2, v_struct_859_);
lean_closure_set(v___f_866_, 3, v_toBind_860_);
lean_closure_set(v___f_866_, 4, v___f_865_);
v___x_867_ = lean_apply_4(v_toBind_860_, lean_box(0), lean_box(0), v_isDebugEnabled_863_, v___f_866_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS(lean_object* v_m_868_, lean_object* v_inst_869_, lean_object* v_inst_870_, lean_object* v_structName_871_, lean_object* v_idx_872_, lean_object* v_struct_873_){
_start:
{
lean_object* v___x_874_; 
v___x_874_ = l_Lean_Meta_Sym_Internal_mkProjS___redArg(v_inst_869_, v_inst_870_, v_structName_871_, v_idx_872_, v_struct_873_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__0(lean_object* v_f_875_, lean_object* v_a_876_, lean_object* v_share1_877_, lean_object* v_____r_878_){
_start:
{
lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_879_ = l_Lean_Expr_app___override(v_f_875_, v_a_876_);
v___x_880_ = lean_apply_1(v_share1_877_, v___x_879_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__2(lean_object* v_assertShared_881_, lean_object* v_a_882_, lean_object* v_toBind_883_, lean_object* v___f_884_, lean_object* v_____r_885_){
_start:
{
lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_886_ = lean_apply_1(v_assertShared_881_, v_a_882_);
v___x_887_ = lean_apply_4(v_toBind_883_, lean_box(0), lean_box(0), v___x_886_, v___f_884_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__1(lean_object* v___f_888_, lean_object* v_assertShared_889_, lean_object* v_a_890_, lean_object* v_toBind_891_, lean_object* v___f_892_, lean_object* v_f_893_, uint8_t v_____do__lift_894_){
_start:
{
if (v_____do__lift_894_ == 0)
{
lean_object* v___x_895_; lean_object* v___x_896_; 
lean_dec_ref(v_f_893_);
lean_dec(v___f_892_);
lean_dec(v_toBind_891_);
lean_dec_ref(v_a_890_);
lean_dec(v_assertShared_889_);
v___x_895_ = lean_box(0);
v___x_896_ = lean_apply_1(v___f_888_, v___x_895_);
return v___x_896_;
}
else
{
lean_object* v___f_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
lean_dec(v___f_888_);
lean_inc(v_toBind_891_);
lean_inc(v_assertShared_889_);
v___f_897_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__2), 5, 4);
lean_closure_set(v___f_897_, 0, v_assertShared_889_);
lean_closure_set(v___f_897_, 1, v_a_890_);
lean_closure_set(v___f_897_, 2, v_toBind_891_);
lean_closure_set(v___f_897_, 3, v___f_892_);
v___x_898_ = lean_apply_1(v_assertShared_889_, v_f_893_);
v___x_899_ = lean_apply_4(v_toBind_891_, lean_box(0), lean_box(0), v___x_898_, v___f_897_);
return v___x_899_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__1___boxed(lean_object* v___f_900_, lean_object* v_assertShared_901_, lean_object* v_a_902_, lean_object* v_toBind_903_, lean_object* v___f_904_, lean_object* v_f_905_, lean_object* v_____do__lift_906_){
_start:
{
uint8_t v_____do__lift_105__boxed_907_; lean_object* v_res_908_; 
v_____do__lift_105__boxed_907_ = lean_unbox(v_____do__lift_906_);
v_res_908_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__1(v___f_900_, v_assertShared_901_, v_a_902_, v_toBind_903_, v___f_904_, v_f_905_, v_____do__lift_105__boxed_907_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg(lean_object* v_inst_909_, lean_object* v_inst_910_, lean_object* v_f_911_, lean_object* v_a_912_){
_start:
{
lean_object* v_toBind_913_; lean_object* v_share1_914_; lean_object* v_assertShared_915_; lean_object* v_isDebugEnabled_916_; lean_object* v___f_917_; lean_object* v___f_918_; lean_object* v___f_919_; lean_object* v___x_920_; 
v_toBind_913_ = lean_ctor_get(v_inst_910_, 1);
lean_inc_n(v_toBind_913_, 2);
lean_dec_ref(v_inst_910_);
v_share1_914_ = lean_ctor_get(v_inst_909_, 0);
lean_inc(v_share1_914_);
v_assertShared_915_ = lean_ctor_get(v_inst_909_, 1);
lean_inc(v_assertShared_915_);
v_isDebugEnabled_916_ = lean_ctor_get(v_inst_909_, 2);
lean_inc(v_isDebugEnabled_916_);
lean_dec_ref(v_inst_909_);
lean_inc_ref(v_a_912_);
lean_inc_ref(v_f_911_);
v___f_917_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__0), 4, 3);
lean_closure_set(v___f_917_, 0, v_f_911_);
lean_closure_set(v___f_917_, 1, v_a_912_);
lean_closure_set(v___f_917_, 2, v_share1_914_);
lean_inc_ref(v___f_917_);
v___f_918_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_918_, 0, v___f_917_);
v___f_919_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_919_, 0, v___f_917_);
lean_closure_set(v___f_919_, 1, v_assertShared_915_);
lean_closure_set(v___f_919_, 2, v_a_912_);
lean_closure_set(v___f_919_, 3, v_toBind_913_);
lean_closure_set(v___f_919_, 4, v___f_918_);
lean_closure_set(v___f_919_, 5, v_f_911_);
v___x_920_ = lean_apply_4(v_toBind_913_, lean_box(0), lean_box(0), v_isDebugEnabled_916_, v___f_919_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS(lean_object* v_m_921_, lean_object* v_inst_922_, lean_object* v_inst_923_, lean_object* v_f_924_, lean_object* v_a_925_){
_start:
{
lean_object* v___x_926_; 
v___x_926_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_922_, v_inst_923_, v_f_924_, v_a_925_);
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__0(lean_object* v_x_927_, lean_object* v_t_928_, lean_object* v_b_929_, uint8_t v_bi_930_, lean_object* v_share1_931_, lean_object* v_____r_932_){
_start:
{
lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_933_ = l_Lean_Expr_lam___override(v_x_927_, v_t_928_, v_b_929_, v_bi_930_);
v___x_934_ = lean_apply_1(v_share1_931_, v___x_933_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__0___boxed(lean_object* v_x_935_, lean_object* v_t_936_, lean_object* v_b_937_, lean_object* v_bi_938_, lean_object* v_share1_939_, lean_object* v_____r_940_){
_start:
{
uint8_t v_bi_boxed_941_; lean_object* v_res_942_; 
v_bi_boxed_941_ = lean_unbox(v_bi_938_);
v_res_942_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__0(v_x_935_, v_t_936_, v_b_937_, v_bi_boxed_941_, v_share1_939_, v_____r_940_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__2(lean_object* v_assertShared_943_, lean_object* v_b_944_, lean_object* v_toBind_945_, lean_object* v___f_946_, lean_object* v_____r_947_){
_start:
{
lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_948_ = lean_apply_1(v_assertShared_943_, v_b_944_);
v___x_949_ = lean_apply_4(v_toBind_945_, lean_box(0), lean_box(0), v___x_948_, v___f_946_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1(lean_object* v___f_950_, lean_object* v_assertShared_951_, lean_object* v_b_952_, lean_object* v_toBind_953_, lean_object* v___f_954_, lean_object* v_t_955_, uint8_t v_____do__lift_956_){
_start:
{
if (v_____do__lift_956_ == 0)
{
lean_object* v___x_957_; lean_object* v___x_958_; 
lean_dec_ref(v_t_955_);
lean_dec(v___f_954_);
lean_dec(v_toBind_953_);
lean_dec_ref(v_b_952_);
lean_dec(v_assertShared_951_);
v___x_957_ = lean_box(0);
v___x_958_ = lean_apply_1(v___f_950_, v___x_957_);
return v___x_958_;
}
else
{
lean_object* v___f_959_; lean_object* v___x_960_; lean_object* v___x_961_; 
lean_dec(v___f_950_);
lean_inc(v_toBind_953_);
lean_inc(v_assertShared_951_);
v___f_959_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__2), 5, 4);
lean_closure_set(v___f_959_, 0, v_assertShared_951_);
lean_closure_set(v___f_959_, 1, v_b_952_);
lean_closure_set(v___f_959_, 2, v_toBind_953_);
lean_closure_set(v___f_959_, 3, v___f_954_);
v___x_960_ = lean_apply_1(v_assertShared_951_, v_t_955_);
v___x_961_ = lean_apply_4(v_toBind_953_, lean_box(0), lean_box(0), v___x_960_, v___f_959_);
return v___x_961_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1___boxed(lean_object* v___f_962_, lean_object* v_assertShared_963_, lean_object* v_b_964_, lean_object* v_toBind_965_, lean_object* v___f_966_, lean_object* v_t_967_, lean_object* v_____do__lift_968_){
_start:
{
uint8_t v_____do__lift_106__boxed_969_; lean_object* v_res_970_; 
v_____do__lift_106__boxed_969_ = lean_unbox(v_____do__lift_968_);
v_res_970_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1(v___f_962_, v_assertShared_963_, v_b_964_, v_toBind_965_, v___f_966_, v_t_967_, v_____do__lift_106__boxed_969_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(lean_object* v_inst_971_, lean_object* v_inst_972_, lean_object* v_x_973_, uint8_t v_bi_974_, lean_object* v_t_975_, lean_object* v_b_976_){
_start:
{
lean_object* v_toBind_977_; lean_object* v_share1_978_; lean_object* v_assertShared_979_; lean_object* v_isDebugEnabled_980_; lean_object* v___x_981_; lean_object* v___f_982_; lean_object* v___f_983_; lean_object* v___f_984_; lean_object* v___x_985_; 
v_toBind_977_ = lean_ctor_get(v_inst_972_, 1);
lean_inc_n(v_toBind_977_, 2);
lean_dec_ref(v_inst_972_);
v_share1_978_ = lean_ctor_get(v_inst_971_, 0);
lean_inc(v_share1_978_);
v_assertShared_979_ = lean_ctor_get(v_inst_971_, 1);
lean_inc(v_assertShared_979_);
v_isDebugEnabled_980_ = lean_ctor_get(v_inst_971_, 2);
lean_inc(v_isDebugEnabled_980_);
lean_dec_ref(v_inst_971_);
v___x_981_ = lean_box(v_bi_974_);
lean_inc_ref(v_b_976_);
lean_inc_ref(v_t_975_);
v___f_982_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_982_, 0, v_x_973_);
lean_closure_set(v___f_982_, 1, v_t_975_);
lean_closure_set(v___f_982_, 2, v_b_976_);
lean_closure_set(v___f_982_, 3, v___x_981_);
lean_closure_set(v___f_982_, 4, v_share1_978_);
lean_inc_ref(v___f_982_);
v___f_983_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_983_, 0, v___f_982_);
v___f_984_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_984_, 0, v___f_982_);
lean_closure_set(v___f_984_, 1, v_assertShared_979_);
lean_closure_set(v___f_984_, 2, v_b_976_);
lean_closure_set(v___f_984_, 3, v_toBind_977_);
lean_closure_set(v___f_984_, 4, v___f_983_);
lean_closure_set(v___f_984_, 5, v_t_975_);
v___x_985_ = lean_apply_4(v_toBind_977_, lean_box(0), lean_box(0), v_isDebugEnabled_980_, v___f_984_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___boxed(lean_object* v_inst_986_, lean_object* v_inst_987_, lean_object* v_x_988_, lean_object* v_bi_989_, lean_object* v_t_990_, lean_object* v_b_991_){
_start:
{
uint8_t v_bi_boxed_992_; lean_object* v_res_993_; 
v_bi_boxed_992_ = lean_unbox(v_bi_989_);
v_res_993_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v_inst_986_, v_inst_987_, v_x_988_, v_bi_boxed_992_, v_t_990_, v_b_991_);
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS(lean_object* v_m_994_, lean_object* v_inst_995_, lean_object* v_inst_996_, lean_object* v_x_997_, uint8_t v_bi_998_, lean_object* v_t_999_, lean_object* v_b_1000_){
_start:
{
lean_object* v___x_1001_; 
v___x_1001_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v_inst_995_, v_inst_996_, v_x_997_, v_bi_998_, v_t_999_, v_b_1000_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___boxed(lean_object* v_m_1002_, lean_object* v_inst_1003_, lean_object* v_inst_1004_, lean_object* v_x_1005_, lean_object* v_bi_1006_, lean_object* v_t_1007_, lean_object* v_b_1008_){
_start:
{
uint8_t v_bi_boxed_1009_; lean_object* v_res_1010_; 
v_bi_boxed_1009_ = lean_unbox(v_bi_1006_);
v_res_1010_ = l_Lean_Meta_Sym_Internal_mkLambdaS(v_m_1002_, v_inst_1003_, v_inst_1004_, v_x_1005_, v_bi_boxed_1009_, v_t_1007_, v_b_1008_);
return v_res_1010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___redArg___lam__0(lean_object* v_x_1011_, lean_object* v_t_1012_, lean_object* v_b_1013_, uint8_t v_bi_1014_, lean_object* v_share1_1015_, lean_object* v_____r_1016_){
_start:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1017_ = l_Lean_Expr_forallE___override(v_x_1011_, v_t_1012_, v_b_1013_, v_bi_1014_);
v___x_1018_ = lean_apply_1(v_share1_1015_, v___x_1017_);
return v___x_1018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___redArg___lam__0___boxed(lean_object* v_x_1019_, lean_object* v_t_1020_, lean_object* v_b_1021_, lean_object* v_bi_1022_, lean_object* v_share1_1023_, lean_object* v_____r_1024_){
_start:
{
uint8_t v_bi_boxed_1025_; lean_object* v_res_1026_; 
v_bi_boxed_1025_ = lean_unbox(v_bi_1022_);
v_res_1026_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg___lam__0(v_x_1019_, v_t_1020_, v_b_1021_, v_bi_boxed_1025_, v_share1_1023_, v_____r_1024_);
return v_res_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___redArg(lean_object* v_inst_1027_, lean_object* v_inst_1028_, lean_object* v_x_1029_, uint8_t v_bi_1030_, lean_object* v_t_1031_, lean_object* v_b_1032_){
_start:
{
lean_object* v_toBind_1033_; lean_object* v_share1_1034_; lean_object* v_assertShared_1035_; lean_object* v_isDebugEnabled_1036_; lean_object* v___x_1037_; lean_object* v___f_1038_; lean_object* v___f_1039_; lean_object* v___f_1040_; lean_object* v___x_1041_; 
v_toBind_1033_ = lean_ctor_get(v_inst_1028_, 1);
lean_inc_n(v_toBind_1033_, 2);
lean_dec_ref(v_inst_1028_);
v_share1_1034_ = lean_ctor_get(v_inst_1027_, 0);
lean_inc(v_share1_1034_);
v_assertShared_1035_ = lean_ctor_get(v_inst_1027_, 1);
lean_inc(v_assertShared_1035_);
v_isDebugEnabled_1036_ = lean_ctor_get(v_inst_1027_, 2);
lean_inc(v_isDebugEnabled_1036_);
lean_dec_ref(v_inst_1027_);
v___x_1037_ = lean_box(v_bi_1030_);
lean_inc_ref(v_b_1032_);
lean_inc_ref(v_t_1031_);
v___f_1038_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkForallS___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1038_, 0, v_x_1029_);
lean_closure_set(v___f_1038_, 1, v_t_1031_);
lean_closure_set(v___f_1038_, 2, v_b_1032_);
lean_closure_set(v___f_1038_, 3, v___x_1037_);
lean_closure_set(v___f_1038_, 4, v_share1_1034_);
lean_inc_ref(v___f_1038_);
v___f_1039_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1039_, 0, v___f_1038_);
v___f_1040_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_1040_, 0, v___f_1038_);
lean_closure_set(v___f_1040_, 1, v_assertShared_1035_);
lean_closure_set(v___f_1040_, 2, v_b_1032_);
lean_closure_set(v___f_1040_, 3, v_toBind_1033_);
lean_closure_set(v___f_1040_, 4, v___f_1039_);
lean_closure_set(v___f_1040_, 5, v_t_1031_);
v___x_1041_ = lean_apply_4(v_toBind_1033_, lean_box(0), lean_box(0), v_isDebugEnabled_1036_, v___f_1040_);
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___redArg___boxed(lean_object* v_inst_1042_, lean_object* v_inst_1043_, lean_object* v_x_1044_, lean_object* v_bi_1045_, lean_object* v_t_1046_, lean_object* v_b_1047_){
_start:
{
uint8_t v_bi_boxed_1048_; lean_object* v_res_1049_; 
v_bi_boxed_1048_ = lean_unbox(v_bi_1045_);
v_res_1049_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v_inst_1042_, v_inst_1043_, v_x_1044_, v_bi_boxed_1048_, v_t_1046_, v_b_1047_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS(lean_object* v_m_1050_, lean_object* v_inst_1051_, lean_object* v_inst_1052_, lean_object* v_x_1053_, uint8_t v_bi_1054_, lean_object* v_t_1055_, lean_object* v_b_1056_){
_start:
{
lean_object* v___x_1057_; 
v___x_1057_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v_inst_1051_, v_inst_1052_, v_x_1053_, v_bi_1054_, v_t_1055_, v_b_1056_);
return v___x_1057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___boxed(lean_object* v_m_1058_, lean_object* v_inst_1059_, lean_object* v_inst_1060_, lean_object* v_x_1061_, lean_object* v_bi_1062_, lean_object* v_t_1063_, lean_object* v_b_1064_){
_start:
{
uint8_t v_bi_boxed_1065_; lean_object* v_res_1066_; 
v_bi_boxed_1065_ = lean_unbox(v_bi_1062_);
v_res_1066_ = l_Lean_Meta_Sym_Internal_mkForallS(v_m_1058_, v_inst_1059_, v_inst_1060_, v_x_1061_, v_bi_boxed_1065_, v_t_1063_, v_b_1064_);
return v_res_1066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__0(lean_object* v_x_1067_, lean_object* v_t_1068_, lean_object* v_v_1069_, lean_object* v_b_1070_, uint8_t v_nondep_1071_, lean_object* v_share1_1072_, lean_object* v_____r_1073_){
_start:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1074_ = l_Lean_Expr_letE___override(v_x_1067_, v_t_1068_, v_v_1069_, v_b_1070_, v_nondep_1071_);
v___x_1075_ = lean_apply_1(v_share1_1072_, v___x_1074_);
return v___x_1075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__0___boxed(lean_object* v_x_1076_, lean_object* v_t_1077_, lean_object* v_v_1078_, lean_object* v_b_1079_, lean_object* v_nondep_1080_, lean_object* v_share1_1081_, lean_object* v_____r_1082_){
_start:
{
uint8_t v_nondep_boxed_1083_; lean_object* v_res_1084_; 
v_nondep_boxed_1083_ = lean_unbox(v_nondep_1080_);
v_res_1084_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__0(v_x_1076_, v_t_1077_, v_v_1078_, v_b_1079_, v_nondep_boxed_1083_, v_share1_1081_, v_____r_1082_);
return v_res_1084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__3(lean_object* v_assertShared_1085_, lean_object* v_v_1086_, lean_object* v_toBind_1087_, lean_object* v___f_1088_, lean_object* v_____r_1089_){
_start:
{
lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1090_ = lean_apply_1(v_assertShared_1085_, v_v_1086_);
v___x_1091_ = lean_apply_4(v_toBind_1087_, lean_box(0), lean_box(0), v___x_1090_, v___f_1088_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1(lean_object* v___f_1092_, lean_object* v_assertShared_1093_, lean_object* v_b_1094_, lean_object* v_toBind_1095_, lean_object* v___f_1096_, lean_object* v_v_1097_, lean_object* v_t_1098_, uint8_t v_____do__lift_1099_){
_start:
{
if (v_____do__lift_1099_ == 0)
{
lean_object* v___x_1100_; lean_object* v___x_1101_; 
lean_dec_ref(v_t_1098_);
lean_dec_ref(v_v_1097_);
lean_dec(v___f_1096_);
lean_dec(v_toBind_1095_);
lean_dec_ref(v_b_1094_);
lean_dec(v_assertShared_1093_);
v___x_1100_ = lean_box(0);
v___x_1101_ = lean_apply_1(v___f_1092_, v___x_1100_);
return v___x_1101_;
}
else
{
lean_object* v___f_1102_; lean_object* v___f_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; 
lean_dec(v___f_1092_);
lean_inc_n(v_toBind_1095_, 2);
lean_inc_n(v_assertShared_1093_, 2);
v___f_1102_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__2), 5, 4);
lean_closure_set(v___f_1102_, 0, v_assertShared_1093_);
lean_closure_set(v___f_1102_, 1, v_b_1094_);
lean_closure_set(v___f_1102_, 2, v_toBind_1095_);
lean_closure_set(v___f_1102_, 3, v___f_1096_);
v___f_1103_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__3), 5, 4);
lean_closure_set(v___f_1103_, 0, v_assertShared_1093_);
lean_closure_set(v___f_1103_, 1, v_v_1097_);
lean_closure_set(v___f_1103_, 2, v_toBind_1095_);
lean_closure_set(v___f_1103_, 3, v___f_1102_);
v___x_1104_ = lean_apply_1(v_assertShared_1093_, v_t_1098_);
v___x_1105_ = lean_apply_4(v_toBind_1095_, lean_box(0), lean_box(0), v___x_1104_, v___f_1103_);
return v___x_1105_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1___boxed(lean_object* v___f_1106_, lean_object* v_assertShared_1107_, lean_object* v_b_1108_, lean_object* v_toBind_1109_, lean_object* v___f_1110_, lean_object* v_v_1111_, lean_object* v_t_1112_, lean_object* v_____do__lift_1113_){
_start:
{
uint8_t v_____do__lift_123__boxed_1114_; lean_object* v_res_1115_; 
v_____do__lift_123__boxed_1114_ = lean_unbox(v_____do__lift_1113_);
v_res_1115_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1(v___f_1106_, v_assertShared_1107_, v_b_1108_, v_toBind_1109_, v___f_1110_, v_v_1111_, v_t_1112_, v_____do__lift_123__boxed_1114_);
return v_res_1115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg(lean_object* v_inst_1116_, lean_object* v_inst_1117_, lean_object* v_x_1118_, lean_object* v_t_1119_, lean_object* v_v_1120_, lean_object* v_b_1121_, uint8_t v_nondep_1122_){
_start:
{
lean_object* v_toBind_1123_; lean_object* v_share1_1124_; lean_object* v_assertShared_1125_; lean_object* v_isDebugEnabled_1126_; lean_object* v___x_1127_; lean_object* v___f_1128_; lean_object* v___f_1129_; lean_object* v___f_1130_; lean_object* v___x_1131_; 
v_toBind_1123_ = lean_ctor_get(v_inst_1117_, 1);
lean_inc_n(v_toBind_1123_, 2);
lean_dec_ref(v_inst_1117_);
v_share1_1124_ = lean_ctor_get(v_inst_1116_, 0);
lean_inc(v_share1_1124_);
v_assertShared_1125_ = lean_ctor_get(v_inst_1116_, 1);
lean_inc(v_assertShared_1125_);
v_isDebugEnabled_1126_ = lean_ctor_get(v_inst_1116_, 2);
lean_inc(v_isDebugEnabled_1126_);
lean_dec_ref(v_inst_1116_);
v___x_1127_ = lean_box(v_nondep_1122_);
lean_inc_ref(v_b_1121_);
lean_inc_ref(v_v_1120_);
lean_inc_ref(v_t_1119_);
v___f_1128_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_1128_, 0, v_x_1118_);
lean_closure_set(v___f_1128_, 1, v_t_1119_);
lean_closure_set(v___f_1128_, 2, v_v_1120_);
lean_closure_set(v___f_1128_, 3, v_b_1121_);
lean_closure_set(v___f_1128_, 4, v___x_1127_);
lean_closure_set(v___f_1128_, 5, v_share1_1124_);
lean_inc_ref(v___f_1128_);
v___f_1129_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1129_, 0, v___f_1128_);
v___f_1130_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_1130_, 0, v___f_1128_);
lean_closure_set(v___f_1130_, 1, v_assertShared_1125_);
lean_closure_set(v___f_1130_, 2, v_b_1121_);
lean_closure_set(v___f_1130_, 3, v_toBind_1123_);
lean_closure_set(v___f_1130_, 4, v___f_1129_);
lean_closure_set(v___f_1130_, 5, v_v_1120_);
lean_closure_set(v___f_1130_, 6, v_t_1119_);
v___x_1131_ = lean_apply_4(v_toBind_1123_, lean_box(0), lean_box(0), v_isDebugEnabled_1126_, v___f_1130_);
return v___x_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___boxed(lean_object* v_inst_1132_, lean_object* v_inst_1133_, lean_object* v_x_1134_, lean_object* v_t_1135_, lean_object* v_v_1136_, lean_object* v_b_1137_, lean_object* v_nondep_1138_){
_start:
{
uint8_t v_nondep_boxed_1139_; lean_object* v_res_1140_; 
v_nondep_boxed_1139_ = lean_unbox(v_nondep_1138_);
v_res_1140_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1132_, v_inst_1133_, v_x_1134_, v_t_1135_, v_v_1136_, v_b_1137_, v_nondep_boxed_1139_);
return v_res_1140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS(lean_object* v_m_1141_, lean_object* v_inst_1142_, lean_object* v_inst_1143_, lean_object* v_x_1144_, lean_object* v_t_1145_, lean_object* v_v_1146_, lean_object* v_b_1147_, uint8_t v_nondep_1148_){
_start:
{
lean_object* v___x_1149_; 
v___x_1149_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1142_, v_inst_1143_, v_x_1144_, v_t_1145_, v_v_1146_, v_b_1147_, v_nondep_1148_);
return v___x_1149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___boxed(lean_object* v_m_1150_, lean_object* v_inst_1151_, lean_object* v_inst_1152_, lean_object* v_x_1153_, lean_object* v_t_1154_, lean_object* v_v_1155_, lean_object* v_b_1156_, lean_object* v_nondep_1157_){
_start:
{
uint8_t v_nondep_boxed_1158_; lean_object* v_res_1159_; 
v_nondep_boxed_1158_ = lean_unbox(v_nondep_1157_);
v_res_1159_ = l_Lean_Meta_Sym_Internal_mkLetS(v_m_1150_, v_inst_1151_, v_inst_1152_, v_x_1153_, v_t_1154_, v_v_1155_, v_b_1156_, v_nondep_boxed_1158_);
return v_res_1159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkHaveS___redArg___lam__0(lean_object* v_x_1160_, lean_object* v_t_1161_, lean_object* v_v_1162_, lean_object* v_b_1163_, lean_object* v_share1_1164_, lean_object* v_____r_1165_){
_start:
{
uint8_t v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1166_ = 1;
v___x_1167_ = l_Lean_Expr_letE___override(v_x_1160_, v_t_1161_, v_v_1162_, v_b_1163_, v___x_1166_);
v___x_1168_ = lean_apply_1(v_share1_1164_, v___x_1167_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkHaveS___redArg(lean_object* v_inst_1169_, lean_object* v_inst_1170_, lean_object* v_x_1171_, lean_object* v_t_1172_, lean_object* v_v_1173_, lean_object* v_b_1174_){
_start:
{
lean_object* v_toBind_1175_; lean_object* v_share1_1176_; lean_object* v_assertShared_1177_; lean_object* v_isDebugEnabled_1178_; lean_object* v___f_1179_; lean_object* v___f_1180_; lean_object* v___f_1181_; lean_object* v___x_1182_; 
v_toBind_1175_ = lean_ctor_get(v_inst_1170_, 1);
lean_inc_n(v_toBind_1175_, 2);
lean_dec_ref(v_inst_1170_);
v_share1_1176_ = lean_ctor_get(v_inst_1169_, 0);
lean_inc(v_share1_1176_);
v_assertShared_1177_ = lean_ctor_get(v_inst_1169_, 1);
lean_inc(v_assertShared_1177_);
v_isDebugEnabled_1178_ = lean_ctor_get(v_inst_1169_, 2);
lean_inc(v_isDebugEnabled_1178_);
lean_dec_ref(v_inst_1169_);
lean_inc_ref(v_b_1174_);
lean_inc_ref(v_v_1173_);
lean_inc_ref(v_t_1172_);
v___f_1179_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkHaveS___redArg___lam__0), 6, 5);
lean_closure_set(v___f_1179_, 0, v_x_1171_);
lean_closure_set(v___f_1179_, 1, v_t_1172_);
lean_closure_set(v___f_1179_, 2, v_v_1173_);
lean_closure_set(v___f_1179_, 3, v_b_1174_);
lean_closure_set(v___f_1179_, 4, v_share1_1176_);
lean_inc_ref(v___f_1179_);
v___f_1180_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1180_, 0, v___f_1179_);
v___f_1181_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_1181_, 0, v___f_1179_);
lean_closure_set(v___f_1181_, 1, v_assertShared_1177_);
lean_closure_set(v___f_1181_, 2, v_b_1174_);
lean_closure_set(v___f_1181_, 3, v_toBind_1175_);
lean_closure_set(v___f_1181_, 4, v___f_1180_);
lean_closure_set(v___f_1181_, 5, v_v_1173_);
lean_closure_set(v___f_1181_, 6, v_t_1172_);
v___x_1182_ = lean_apply_4(v_toBind_1175_, lean_box(0), lean_box(0), v_isDebugEnabled_1178_, v___f_1181_);
return v___x_1182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkHaveS(lean_object* v_m_1183_, lean_object* v_inst_1184_, lean_object* v_inst_1185_, lean_object* v_x_1186_, lean_object* v_t_1187_, lean_object* v_v_1188_, lean_object* v_b_1189_){
_start:
{
lean_object* v___x_1190_; 
v___x_1190_ = l_Lean_Meta_Sym_Internal_mkHaveS___redArg(v_inst_1184_, v_inst_1185_, v_x_1186_, v_t_1187_, v_v_1188_, v_b_1189_);
return v___x_1190_;
}
}
static lean_object* _init_l_Lean_Expr_updateAppS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1193_ = ((lean_object*)(l_Lean_Expr_updateAppS_x21___redArg___closed__1));
v___x_1194_ = lean_unsigned_to_nat(25u);
v___x_1195_ = lean_unsigned_to_nat(148u);
v___x_1196_ = ((lean_object*)(l_Lean_Expr_updateAppS_x21___redArg___closed__0));
v___x_1197_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1198_ = l_mkPanicMessageWithDecl(v___x_1197_, v___x_1196_, v___x_1195_, v___x_1194_, v___x_1193_);
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateAppS_x21___redArg(lean_object* v_inst_1199_, lean_object* v_inst_1200_, lean_object* v_e_1201_, lean_object* v_newFn_1202_, lean_object* v_newArg_1203_){
_start:
{
uint8_t v___y_1205_; 
if (lean_obj_tag(v_e_1201_) == 5)
{
lean_object* v_fn_1210_; lean_object* v_arg_1211_; uint8_t v___x_1212_; 
v_fn_1210_ = lean_ctor_get(v_e_1201_, 0);
v_arg_1211_ = lean_ctor_get(v_e_1201_, 1);
v___x_1212_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fn_1210_, v_newFn_1202_);
if (v___x_1212_ == 0)
{
v___y_1205_ = v___x_1212_;
goto v___jp_1204_;
}
else
{
uint8_t v___x_1213_; 
v___x_1213_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_1211_, v_newArg_1203_);
v___y_1205_ = v___x_1213_;
goto v___jp_1204_;
}
}
else
{
lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
lean_dec_ref(v_newArg_1203_);
lean_dec_ref(v_newFn_1202_);
lean_dec_ref(v_e_1201_);
lean_dec_ref(v_inst_1199_);
v___x_1214_ = l_Lean_instInhabitedExpr;
v___x_1215_ = l_instInhabitedOfMonad___redArg(v_inst_1200_, v___x_1214_);
v___x_1216_ = lean_obj_once(&l_Lean_Expr_updateAppS_x21___redArg___closed__2, &l_Lean_Expr_updateAppS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateAppS_x21___redArg___closed__2);
v___x_1217_ = l_panic___redArg(v___x_1215_, v___x_1216_);
lean_dec(v___x_1215_);
return v___x_1217_;
}
v___jp_1204_:
{
if (v___y_1205_ == 0)
{
lean_object* v___x_1206_; 
lean_dec_ref(v_e_1201_);
v___x_1206_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1199_, v_inst_1200_, v_newFn_1202_, v_newArg_1203_);
return v___x_1206_;
}
else
{
lean_object* v_toApplicative_1207_; lean_object* v_toPure_1208_; lean_object* v___x_1209_; 
lean_dec_ref(v_newArg_1203_);
lean_dec_ref(v_newFn_1202_);
lean_dec_ref(v_inst_1199_);
v_toApplicative_1207_ = lean_ctor_get(v_inst_1200_, 0);
lean_inc_ref(v_toApplicative_1207_);
lean_dec_ref(v_inst_1200_);
v_toPure_1208_ = lean_ctor_get(v_toApplicative_1207_, 1);
lean_inc(v_toPure_1208_);
lean_dec_ref(v_toApplicative_1207_);
v___x_1209_ = lean_apply_2(v_toPure_1208_, lean_box(0), v_e_1201_);
return v___x_1209_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateAppS_x21(lean_object* v_m_1218_, lean_object* v_inst_1219_, lean_object* v_inst_1220_, lean_object* v_e_1221_, lean_object* v_newFn_1222_, lean_object* v_newArg_1223_){
_start:
{
uint8_t v___y_1225_; 
if (lean_obj_tag(v_e_1221_) == 5)
{
lean_object* v_fn_1230_; lean_object* v_arg_1231_; uint8_t v___x_1232_; 
v_fn_1230_ = lean_ctor_get(v_e_1221_, 0);
v_arg_1231_ = lean_ctor_get(v_e_1221_, 1);
v___x_1232_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fn_1230_, v_newFn_1222_);
if (v___x_1232_ == 0)
{
v___y_1225_ = v___x_1232_;
goto v___jp_1224_;
}
else
{
uint8_t v___x_1233_; 
v___x_1233_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_1231_, v_newArg_1223_);
v___y_1225_ = v___x_1233_;
goto v___jp_1224_;
}
}
else
{
lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; 
lean_dec_ref(v_newArg_1223_);
lean_dec_ref(v_newFn_1222_);
lean_dec_ref(v_e_1221_);
lean_dec_ref(v_inst_1219_);
v___x_1234_ = l_Lean_instInhabitedExpr;
v___x_1235_ = l_instInhabitedOfMonad___redArg(v_inst_1220_, v___x_1234_);
v___x_1236_ = lean_obj_once(&l_Lean_Expr_updateAppS_x21___redArg___closed__2, &l_Lean_Expr_updateAppS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateAppS_x21___redArg___closed__2);
v___x_1237_ = l_panic___redArg(v___x_1235_, v___x_1236_);
lean_dec(v___x_1235_);
return v___x_1237_;
}
v___jp_1224_:
{
if (v___y_1225_ == 0)
{
lean_object* v___x_1226_; 
lean_dec_ref(v_e_1221_);
v___x_1226_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1219_, v_inst_1220_, v_newFn_1222_, v_newArg_1223_);
return v___x_1226_;
}
else
{
lean_object* v_toApplicative_1227_; lean_object* v_toPure_1228_; lean_object* v___x_1229_; 
lean_dec_ref(v_newArg_1223_);
lean_dec_ref(v_newFn_1222_);
lean_dec_ref(v_inst_1219_);
v_toApplicative_1227_ = lean_ctor_get(v_inst_1220_, 0);
lean_inc_ref(v_toApplicative_1227_);
lean_dec_ref(v_inst_1220_);
v_toPure_1228_ = lean_ctor_get(v_toApplicative_1227_, 1);
lean_inc(v_toPure_1228_);
lean_dec_ref(v_toApplicative_1227_);
v___x_1229_ = lean_apply_2(v_toPure_1228_, lean_box(0), v_e_1221_);
return v___x_1229_;
}
}
}
}
static lean_object* _init_l_Lean_Expr_updateMDataS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1240_ = ((lean_object*)(l_Lean_Expr_updateMDataS_x21___redArg___closed__1));
v___x_1241_ = lean_unsigned_to_nat(24u);
v___x_1242_ = lean_unsigned_to_nat(152u);
v___x_1243_ = ((lean_object*)(l_Lean_Expr_updateMDataS_x21___redArg___closed__0));
v___x_1244_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1245_ = l_mkPanicMessageWithDecl(v___x_1244_, v___x_1243_, v___x_1242_, v___x_1241_, v___x_1240_);
return v___x_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateMDataS_x21___redArg(lean_object* v_inst_1246_, lean_object* v_inst_1247_, lean_object* v_e_1248_, lean_object* v_newExpr_1249_){
_start:
{
if (lean_obj_tag(v_e_1248_) == 10)
{
lean_object* v_data_1250_; lean_object* v_expr_1251_; uint8_t v___x_1252_; 
v_data_1250_ = lean_ctor_get(v_e_1248_, 0);
v_expr_1251_ = lean_ctor_get(v_e_1248_, 1);
v___x_1252_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_expr_1251_, v_newExpr_1249_);
if (v___x_1252_ == 0)
{
lean_object* v___x_1253_; 
lean_inc(v_data_1250_);
lean_dec_ref_known(v_e_1248_, 2);
v___x_1253_ = l_Lean_Meta_Sym_Internal_mkMDataS___redArg(v_inst_1246_, v_inst_1247_, v_data_1250_, v_newExpr_1249_);
return v___x_1253_;
}
else
{
lean_object* v_toApplicative_1254_; lean_object* v_toPure_1255_; lean_object* v___x_1256_; 
lean_dec_ref(v_newExpr_1249_);
lean_dec_ref(v_inst_1246_);
v_toApplicative_1254_ = lean_ctor_get(v_inst_1247_, 0);
lean_inc_ref(v_toApplicative_1254_);
lean_dec_ref(v_inst_1247_);
v_toPure_1255_ = lean_ctor_get(v_toApplicative_1254_, 1);
lean_inc(v_toPure_1255_);
lean_dec_ref(v_toApplicative_1254_);
v___x_1256_ = lean_apply_2(v_toPure_1255_, lean_box(0), v_e_1248_);
return v___x_1256_;
}
}
else
{
lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; 
lean_dec_ref(v_newExpr_1249_);
lean_dec_ref(v_e_1248_);
lean_dec_ref(v_inst_1246_);
v___x_1257_ = l_Lean_instInhabitedExpr;
v___x_1258_ = l_instInhabitedOfMonad___redArg(v_inst_1247_, v___x_1257_);
v___x_1259_ = lean_obj_once(&l_Lean_Expr_updateMDataS_x21___redArg___closed__2, &l_Lean_Expr_updateMDataS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateMDataS_x21___redArg___closed__2);
v___x_1260_ = l_panic___redArg(v___x_1258_, v___x_1259_);
lean_dec(v___x_1258_);
return v___x_1260_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateMDataS_x21(lean_object* v_m_1261_, lean_object* v_inst_1262_, lean_object* v_inst_1263_, lean_object* v_e_1264_, lean_object* v_newExpr_1265_){
_start:
{
if (lean_obj_tag(v_e_1264_) == 10)
{
lean_object* v_data_1266_; lean_object* v_expr_1267_; uint8_t v___x_1268_; 
v_data_1266_ = lean_ctor_get(v_e_1264_, 0);
v_expr_1267_ = lean_ctor_get(v_e_1264_, 1);
v___x_1268_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_expr_1267_, v_newExpr_1265_);
if (v___x_1268_ == 0)
{
lean_object* v___x_1269_; 
lean_inc(v_data_1266_);
lean_dec_ref_known(v_e_1264_, 2);
v___x_1269_ = l_Lean_Meta_Sym_Internal_mkMDataS___redArg(v_inst_1262_, v_inst_1263_, v_data_1266_, v_newExpr_1265_);
return v___x_1269_;
}
else
{
lean_object* v_toApplicative_1270_; lean_object* v_toPure_1271_; lean_object* v___x_1272_; 
lean_dec_ref(v_newExpr_1265_);
lean_dec_ref(v_inst_1262_);
v_toApplicative_1270_ = lean_ctor_get(v_inst_1263_, 0);
lean_inc_ref(v_toApplicative_1270_);
lean_dec_ref(v_inst_1263_);
v_toPure_1271_ = lean_ctor_get(v_toApplicative_1270_, 1);
lean_inc(v_toPure_1271_);
lean_dec_ref(v_toApplicative_1270_);
v___x_1272_ = lean_apply_2(v_toPure_1271_, lean_box(0), v_e_1264_);
return v___x_1272_;
}
}
else
{
lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; 
lean_dec_ref(v_newExpr_1265_);
lean_dec_ref(v_e_1264_);
lean_dec_ref(v_inst_1262_);
v___x_1273_ = l_Lean_instInhabitedExpr;
v___x_1274_ = l_instInhabitedOfMonad___redArg(v_inst_1263_, v___x_1273_);
v___x_1275_ = lean_obj_once(&l_Lean_Expr_updateMDataS_x21___redArg___closed__2, &l_Lean_Expr_updateMDataS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateMDataS_x21___redArg___closed__2);
v___x_1276_ = l_panic___redArg(v___x_1274_, v___x_1275_);
lean_dec(v___x_1274_);
return v___x_1276_;
}
}
}
static lean_object* _init_l_Lean_Expr_updateProjS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1279_ = ((lean_object*)(l_Lean_Expr_updateProjS_x21___redArg___closed__1));
v___x_1280_ = lean_unsigned_to_nat(25u);
v___x_1281_ = lean_unsigned_to_nat(156u);
v___x_1282_ = ((lean_object*)(l_Lean_Expr_updateProjS_x21___redArg___closed__0));
v___x_1283_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1284_ = l_mkPanicMessageWithDecl(v___x_1283_, v___x_1282_, v___x_1281_, v___x_1280_, v___x_1279_);
return v___x_1284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateProjS_x21___redArg(lean_object* v_inst_1285_, lean_object* v_inst_1286_, lean_object* v_e_1287_, lean_object* v_newExpr_1288_){
_start:
{
if (lean_obj_tag(v_e_1287_) == 11)
{
lean_object* v_typeName_1289_; lean_object* v_idx_1290_; lean_object* v_struct_1291_; uint8_t v___x_1292_; 
v_typeName_1289_ = lean_ctor_get(v_e_1287_, 0);
v_idx_1290_ = lean_ctor_get(v_e_1287_, 1);
v_struct_1291_ = lean_ctor_get(v_e_1287_, 2);
v___x_1292_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_1291_, v_newExpr_1288_);
if (v___x_1292_ == 0)
{
lean_object* v___x_1293_; 
lean_inc(v_idx_1290_);
lean_inc(v_typeName_1289_);
lean_dec_ref_known(v_e_1287_, 3);
v___x_1293_ = l_Lean_Meta_Sym_Internal_mkProjS___redArg(v_inst_1285_, v_inst_1286_, v_typeName_1289_, v_idx_1290_, v_newExpr_1288_);
return v___x_1293_;
}
else
{
lean_object* v_toApplicative_1294_; lean_object* v_toPure_1295_; lean_object* v___x_1296_; 
lean_dec_ref(v_newExpr_1288_);
lean_dec_ref(v_inst_1285_);
v_toApplicative_1294_ = lean_ctor_get(v_inst_1286_, 0);
lean_inc_ref(v_toApplicative_1294_);
lean_dec_ref(v_inst_1286_);
v_toPure_1295_ = lean_ctor_get(v_toApplicative_1294_, 1);
lean_inc(v_toPure_1295_);
lean_dec_ref(v_toApplicative_1294_);
v___x_1296_ = lean_apply_2(v_toPure_1295_, lean_box(0), v_e_1287_);
return v___x_1296_;
}
}
else
{
lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
lean_dec_ref(v_newExpr_1288_);
lean_dec_ref(v_e_1287_);
lean_dec_ref(v_inst_1285_);
v___x_1297_ = l_Lean_instInhabitedExpr;
v___x_1298_ = l_instInhabitedOfMonad___redArg(v_inst_1286_, v___x_1297_);
v___x_1299_ = lean_obj_once(&l_Lean_Expr_updateProjS_x21___redArg___closed__2, &l_Lean_Expr_updateProjS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateProjS_x21___redArg___closed__2);
v___x_1300_ = l_panic___redArg(v___x_1298_, v___x_1299_);
lean_dec(v___x_1298_);
return v___x_1300_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateProjS_x21(lean_object* v_m_1301_, lean_object* v_inst_1302_, lean_object* v_inst_1303_, lean_object* v_e_1304_, lean_object* v_newExpr_1305_){
_start:
{
if (lean_obj_tag(v_e_1304_) == 11)
{
lean_object* v_typeName_1306_; lean_object* v_idx_1307_; lean_object* v_struct_1308_; uint8_t v___x_1309_; 
v_typeName_1306_ = lean_ctor_get(v_e_1304_, 0);
v_idx_1307_ = lean_ctor_get(v_e_1304_, 1);
v_struct_1308_ = lean_ctor_get(v_e_1304_, 2);
v___x_1309_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_1308_, v_newExpr_1305_);
if (v___x_1309_ == 0)
{
lean_object* v___x_1310_; 
lean_inc(v_idx_1307_);
lean_inc(v_typeName_1306_);
lean_dec_ref_known(v_e_1304_, 3);
v___x_1310_ = l_Lean_Meta_Sym_Internal_mkProjS___redArg(v_inst_1302_, v_inst_1303_, v_typeName_1306_, v_idx_1307_, v_newExpr_1305_);
return v___x_1310_;
}
else
{
lean_object* v_toApplicative_1311_; lean_object* v_toPure_1312_; lean_object* v___x_1313_; 
lean_dec_ref(v_newExpr_1305_);
lean_dec_ref(v_inst_1302_);
v_toApplicative_1311_ = lean_ctor_get(v_inst_1303_, 0);
lean_inc_ref(v_toApplicative_1311_);
lean_dec_ref(v_inst_1303_);
v_toPure_1312_ = lean_ctor_get(v_toApplicative_1311_, 1);
lean_inc(v_toPure_1312_);
lean_dec_ref(v_toApplicative_1311_);
v___x_1313_ = lean_apply_2(v_toPure_1312_, lean_box(0), v_e_1304_);
return v___x_1313_;
}
}
else
{
lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; 
lean_dec_ref(v_newExpr_1305_);
lean_dec_ref(v_e_1304_);
lean_dec_ref(v_inst_1302_);
v___x_1314_ = l_Lean_instInhabitedExpr;
v___x_1315_ = l_instInhabitedOfMonad___redArg(v_inst_1303_, v___x_1314_);
v___x_1316_ = lean_obj_once(&l_Lean_Expr_updateProjS_x21___redArg___closed__2, &l_Lean_Expr_updateProjS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateProjS_x21___redArg___closed__2);
v___x_1317_ = l_panic___redArg(v___x_1315_, v___x_1316_);
lean_dec(v___x_1315_);
return v___x_1317_;
}
}
}
static lean_object* _init_l_Lean_Expr_updateForallS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; 
v___x_1320_ = ((lean_object*)(l_Lean_Expr_updateForallS_x21___redArg___closed__1));
v___x_1321_ = lean_unsigned_to_nat(31u);
v___x_1322_ = lean_unsigned_to_nat(160u);
v___x_1323_ = ((lean_object*)(l_Lean_Expr_updateForallS_x21___redArg___closed__0));
v___x_1324_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1325_ = l_mkPanicMessageWithDecl(v___x_1324_, v___x_1323_, v___x_1322_, v___x_1321_, v___x_1320_);
return v___x_1325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallS_x21___redArg(lean_object* v_inst_1326_, lean_object* v_inst_1327_, lean_object* v_e_1328_, lean_object* v_newDomain_1329_, lean_object* v_newBody_1330_){
_start:
{
if (lean_obj_tag(v_e_1328_) == 7)
{
lean_object* v_binderName_1331_; lean_object* v_binderType_1332_; lean_object* v_body_1333_; uint8_t v_binderInfo_1334_; uint8_t v___y_1336_; uint8_t v___x_1341_; 
v_binderName_1331_ = lean_ctor_get(v_e_1328_, 0);
v_binderType_1332_ = lean_ctor_get(v_e_1328_, 1);
v_body_1333_ = lean_ctor_get(v_e_1328_, 2);
v_binderInfo_1334_ = lean_ctor_get_uint8(v_e_1328_, sizeof(void*)*3 + 8);
v___x_1341_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_1332_, v_newDomain_1329_);
if (v___x_1341_ == 0)
{
v___y_1336_ = v___x_1341_;
goto v___jp_1335_;
}
else
{
uint8_t v___x_1342_; 
v___x_1342_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1333_, v_newBody_1330_);
v___y_1336_ = v___x_1342_;
goto v___jp_1335_;
}
v___jp_1335_:
{
if (v___y_1336_ == 0)
{
lean_object* v___x_1337_; 
lean_inc(v_binderName_1331_);
lean_dec_ref_known(v_e_1328_, 3);
v___x_1337_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v_inst_1326_, v_inst_1327_, v_binderName_1331_, v_binderInfo_1334_, v_newDomain_1329_, v_newBody_1330_);
return v___x_1337_;
}
else
{
lean_object* v_toApplicative_1338_; lean_object* v_toPure_1339_; lean_object* v___x_1340_; 
lean_dec_ref(v_newBody_1330_);
lean_dec_ref(v_newDomain_1329_);
lean_dec_ref(v_inst_1326_);
v_toApplicative_1338_ = lean_ctor_get(v_inst_1327_, 0);
lean_inc_ref(v_toApplicative_1338_);
lean_dec_ref(v_inst_1327_);
v_toPure_1339_ = lean_ctor_get(v_toApplicative_1338_, 1);
lean_inc(v_toPure_1339_);
lean_dec_ref(v_toApplicative_1338_);
v___x_1340_ = lean_apply_2(v_toPure_1339_, lean_box(0), v_e_1328_);
return v___x_1340_;
}
}
}
else
{
lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; 
lean_dec_ref(v_newBody_1330_);
lean_dec_ref(v_newDomain_1329_);
lean_dec_ref(v_e_1328_);
lean_dec_ref(v_inst_1326_);
v___x_1343_ = l_Lean_instInhabitedExpr;
v___x_1344_ = l_instInhabitedOfMonad___redArg(v_inst_1327_, v___x_1343_);
v___x_1345_ = lean_obj_once(&l_Lean_Expr_updateForallS_x21___redArg___closed__2, &l_Lean_Expr_updateForallS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateForallS_x21___redArg___closed__2);
v___x_1346_ = l_panic___redArg(v___x_1344_, v___x_1345_);
lean_dec(v___x_1344_);
return v___x_1346_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallS_x21(lean_object* v_m_1347_, lean_object* v_inst_1348_, lean_object* v_inst_1349_, lean_object* v_e_1350_, lean_object* v_newDomain_1351_, lean_object* v_newBody_1352_){
_start:
{
if (lean_obj_tag(v_e_1350_) == 7)
{
lean_object* v_binderName_1353_; lean_object* v_binderType_1354_; lean_object* v_body_1355_; uint8_t v_binderInfo_1356_; uint8_t v___y_1358_; uint8_t v___x_1363_; 
v_binderName_1353_ = lean_ctor_get(v_e_1350_, 0);
v_binderType_1354_ = lean_ctor_get(v_e_1350_, 1);
v_body_1355_ = lean_ctor_get(v_e_1350_, 2);
v_binderInfo_1356_ = lean_ctor_get_uint8(v_e_1350_, sizeof(void*)*3 + 8);
v___x_1363_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_1354_, v_newDomain_1351_);
if (v___x_1363_ == 0)
{
v___y_1358_ = v___x_1363_;
goto v___jp_1357_;
}
else
{
uint8_t v___x_1364_; 
v___x_1364_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1355_, v_newBody_1352_);
v___y_1358_ = v___x_1364_;
goto v___jp_1357_;
}
v___jp_1357_:
{
if (v___y_1358_ == 0)
{
lean_object* v___x_1359_; 
lean_inc(v_binderName_1353_);
lean_dec_ref_known(v_e_1350_, 3);
v___x_1359_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v_inst_1348_, v_inst_1349_, v_binderName_1353_, v_binderInfo_1356_, v_newDomain_1351_, v_newBody_1352_);
return v___x_1359_;
}
else
{
lean_object* v_toApplicative_1360_; lean_object* v_toPure_1361_; lean_object* v___x_1362_; 
lean_dec_ref(v_newBody_1352_);
lean_dec_ref(v_newDomain_1351_);
lean_dec_ref(v_inst_1348_);
v_toApplicative_1360_ = lean_ctor_get(v_inst_1349_, 0);
lean_inc_ref(v_toApplicative_1360_);
lean_dec_ref(v_inst_1349_);
v_toPure_1361_ = lean_ctor_get(v_toApplicative_1360_, 1);
lean_inc(v_toPure_1361_);
lean_dec_ref(v_toApplicative_1360_);
v___x_1362_ = lean_apply_2(v_toPure_1361_, lean_box(0), v_e_1350_);
return v___x_1362_;
}
}
}
else
{
lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; 
lean_dec_ref(v_newBody_1352_);
lean_dec_ref(v_newDomain_1351_);
lean_dec_ref(v_e_1350_);
lean_dec_ref(v_inst_1348_);
v___x_1365_ = l_Lean_instInhabitedExpr;
v___x_1366_ = l_instInhabitedOfMonad___redArg(v_inst_1349_, v___x_1365_);
v___x_1367_ = lean_obj_once(&l_Lean_Expr_updateForallS_x21___redArg___closed__2, &l_Lean_Expr_updateForallS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateForallS_x21___redArg___closed__2);
v___x_1368_ = l_panic___redArg(v___x_1366_, v___x_1367_);
lean_dec(v___x_1366_);
return v___x_1368_;
}
}
}
static lean_object* _init_l_Lean_Expr_updateLambdaS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; 
v___x_1371_ = ((lean_object*)(l_Lean_Expr_updateLambdaS_x21___redArg___closed__1));
v___x_1372_ = lean_unsigned_to_nat(27u);
v___x_1373_ = lean_unsigned_to_nat(167u);
v___x_1374_ = ((lean_object*)(l_Lean_Expr_updateLambdaS_x21___redArg___closed__0));
v___x_1375_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1376_ = l_mkPanicMessageWithDecl(v___x_1375_, v___x_1374_, v___x_1373_, v___x_1372_, v___x_1371_);
return v___x_1376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLambdaS_x21___redArg(lean_object* v_inst_1377_, lean_object* v_inst_1378_, lean_object* v_e_1379_, lean_object* v_newDomain_1380_, lean_object* v_newBody_1381_){
_start:
{
if (lean_obj_tag(v_e_1379_) == 6)
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
lean_dec_ref_known(v_e_1379_, 3);
v___x_1388_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v_inst_1377_, v_inst_1378_, v_binderName_1382_, v_binderInfo_1385_, v_newDomain_1380_, v_newBody_1381_);
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
v___x_1396_ = lean_obj_once(&l_Lean_Expr_updateLambdaS_x21___redArg___closed__2, &l_Lean_Expr_updateLambdaS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateLambdaS_x21___redArg___closed__2);
v___x_1397_ = l_panic___redArg(v___x_1395_, v___x_1396_);
lean_dec(v___x_1395_);
return v___x_1397_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLambdaS_x21(lean_object* v_m_1398_, lean_object* v_inst_1399_, lean_object* v_inst_1400_, lean_object* v_e_1401_, lean_object* v_newDomain_1402_, lean_object* v_newBody_1403_){
_start:
{
if (lean_obj_tag(v_e_1401_) == 6)
{
lean_object* v_binderName_1404_; lean_object* v_binderType_1405_; lean_object* v_body_1406_; uint8_t v_binderInfo_1407_; uint8_t v___y_1409_; uint8_t v___x_1414_; 
v_binderName_1404_ = lean_ctor_get(v_e_1401_, 0);
v_binderType_1405_ = lean_ctor_get(v_e_1401_, 1);
v_body_1406_ = lean_ctor_get(v_e_1401_, 2);
v_binderInfo_1407_ = lean_ctor_get_uint8(v_e_1401_, sizeof(void*)*3 + 8);
v___x_1414_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_1405_, v_newDomain_1402_);
if (v___x_1414_ == 0)
{
v___y_1409_ = v___x_1414_;
goto v___jp_1408_;
}
else
{
uint8_t v___x_1415_; 
v___x_1415_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1406_, v_newBody_1403_);
v___y_1409_ = v___x_1415_;
goto v___jp_1408_;
}
v___jp_1408_:
{
if (v___y_1409_ == 0)
{
lean_object* v___x_1410_; 
lean_inc(v_binderName_1404_);
lean_dec_ref_known(v_e_1401_, 3);
v___x_1410_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v_inst_1399_, v_inst_1400_, v_binderName_1404_, v_binderInfo_1407_, v_newDomain_1402_, v_newBody_1403_);
return v___x_1410_;
}
else
{
lean_object* v_toApplicative_1411_; lean_object* v_toPure_1412_; lean_object* v___x_1413_; 
lean_dec_ref(v_newBody_1403_);
lean_dec_ref(v_newDomain_1402_);
lean_dec_ref(v_inst_1399_);
v_toApplicative_1411_ = lean_ctor_get(v_inst_1400_, 0);
lean_inc_ref(v_toApplicative_1411_);
lean_dec_ref(v_inst_1400_);
v_toPure_1412_ = lean_ctor_get(v_toApplicative_1411_, 1);
lean_inc(v_toPure_1412_);
lean_dec_ref(v_toApplicative_1411_);
v___x_1413_ = lean_apply_2(v_toPure_1412_, lean_box(0), v_e_1401_);
return v___x_1413_;
}
}
}
else
{
lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; 
lean_dec_ref(v_newBody_1403_);
lean_dec_ref(v_newDomain_1402_);
lean_dec_ref(v_e_1401_);
lean_dec_ref(v_inst_1399_);
v___x_1416_ = l_Lean_instInhabitedExpr;
v___x_1417_ = l_instInhabitedOfMonad___redArg(v_inst_1400_, v___x_1416_);
v___x_1418_ = lean_obj_once(&l_Lean_Expr_updateLambdaS_x21___redArg___closed__2, &l_Lean_Expr_updateLambdaS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateLambdaS_x21___redArg___closed__2);
v___x_1419_ = l_panic___redArg(v___x_1417_, v___x_1418_);
lean_dec(v___x_1417_);
return v___x_1419_;
}
}
}
static lean_object* _init_l_Lean_Expr_updateLetS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; 
v___x_1422_ = ((lean_object*)(l_Lean_Expr_updateLetS_x21___redArg___closed__1));
v___x_1423_ = lean_unsigned_to_nat(34u);
v___x_1424_ = lean_unsigned_to_nat(174u);
v___x_1425_ = ((lean_object*)(l_Lean_Expr_updateLetS_x21___redArg___closed__0));
v___x_1426_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1427_ = l_mkPanicMessageWithDecl(v___x_1426_, v___x_1425_, v___x_1424_, v___x_1423_, v___x_1422_);
return v___x_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLetS_x21___redArg(lean_object* v_inst_1428_, lean_object* v_inst_1429_, lean_object* v_e_1430_, lean_object* v_newType_1431_, lean_object* v_newVal_1432_, lean_object* v_newBody_1433_){
_start:
{
if (lean_obj_tag(v_e_1430_) == 8)
{
lean_object* v_declName_1434_; lean_object* v_type_1435_; lean_object* v_value_1436_; lean_object* v_body_1437_; uint8_t v_nondep_1438_; uint8_t v___y_1440_; uint8_t v___x_1447_; 
v_declName_1434_ = lean_ctor_get(v_e_1430_, 0);
v_type_1435_ = lean_ctor_get(v_e_1430_, 1);
v_value_1436_ = lean_ctor_get(v_e_1430_, 2);
v_body_1437_ = lean_ctor_get(v_e_1430_, 3);
v_nondep_1438_ = lean_ctor_get_uint8(v_e_1430_, sizeof(void*)*4 + 8);
v___x_1447_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_type_1435_, v_newType_1431_);
if (v___x_1447_ == 0)
{
v___y_1440_ = v___x_1447_;
goto v___jp_1439_;
}
else
{
uint8_t v___x_1448_; 
v___x_1448_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_value_1436_, v_newVal_1432_);
v___y_1440_ = v___x_1448_;
goto v___jp_1439_;
}
v___jp_1439_:
{
if (v___y_1440_ == 0)
{
lean_object* v___x_1441_; 
lean_inc(v_declName_1434_);
lean_dec_ref_known(v_e_1430_, 4);
v___x_1441_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1428_, v_inst_1429_, v_declName_1434_, v_newType_1431_, v_newVal_1432_, v_newBody_1433_, v_nondep_1438_);
return v___x_1441_;
}
else
{
uint8_t v___x_1442_; 
v___x_1442_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1437_, v_newBody_1433_);
if (v___x_1442_ == 0)
{
lean_object* v___x_1443_; 
lean_inc(v_declName_1434_);
lean_dec_ref_known(v_e_1430_, 4);
v___x_1443_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1428_, v_inst_1429_, v_declName_1434_, v_newType_1431_, v_newVal_1432_, v_newBody_1433_, v_nondep_1438_);
return v___x_1443_;
}
else
{
lean_object* v_toApplicative_1444_; lean_object* v_toPure_1445_; lean_object* v___x_1446_; 
lean_dec_ref(v_newBody_1433_);
lean_dec_ref(v_newVal_1432_);
lean_dec_ref(v_newType_1431_);
lean_dec_ref(v_inst_1428_);
v_toApplicative_1444_ = lean_ctor_get(v_inst_1429_, 0);
lean_inc_ref(v_toApplicative_1444_);
lean_dec_ref(v_inst_1429_);
v_toPure_1445_ = lean_ctor_get(v_toApplicative_1444_, 1);
lean_inc(v_toPure_1445_);
lean_dec_ref(v_toApplicative_1444_);
v___x_1446_ = lean_apply_2(v_toPure_1445_, lean_box(0), v_e_1430_);
return v___x_1446_;
}
}
}
}
else
{
lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; 
lean_dec_ref(v_newBody_1433_);
lean_dec_ref(v_newVal_1432_);
lean_dec_ref(v_newType_1431_);
lean_dec_ref(v_e_1430_);
lean_dec_ref(v_inst_1428_);
v___x_1449_ = l_Lean_instInhabitedExpr;
v___x_1450_ = l_instInhabitedOfMonad___redArg(v_inst_1429_, v___x_1449_);
v___x_1451_ = lean_obj_once(&l_Lean_Expr_updateLetS_x21___redArg___closed__2, &l_Lean_Expr_updateLetS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateLetS_x21___redArg___closed__2);
v___x_1452_ = l_panic___redArg(v___x_1450_, v___x_1451_);
lean_dec(v___x_1450_);
return v___x_1452_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLetS_x21(lean_object* v_m_1453_, lean_object* v_inst_1454_, lean_object* v_inst_1455_, lean_object* v_e_1456_, lean_object* v_newType_1457_, lean_object* v_newVal_1458_, lean_object* v_newBody_1459_){
_start:
{
if (lean_obj_tag(v_e_1456_) == 8)
{
lean_object* v_declName_1460_; lean_object* v_type_1461_; lean_object* v_value_1462_; lean_object* v_body_1463_; uint8_t v_nondep_1464_; uint8_t v___y_1466_; uint8_t v___x_1473_; 
v_declName_1460_ = lean_ctor_get(v_e_1456_, 0);
v_type_1461_ = lean_ctor_get(v_e_1456_, 1);
v_value_1462_ = lean_ctor_get(v_e_1456_, 2);
v_body_1463_ = lean_ctor_get(v_e_1456_, 3);
v_nondep_1464_ = lean_ctor_get_uint8(v_e_1456_, sizeof(void*)*4 + 8);
v___x_1473_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_type_1461_, v_newType_1457_);
if (v___x_1473_ == 0)
{
v___y_1466_ = v___x_1473_;
goto v___jp_1465_;
}
else
{
uint8_t v___x_1474_; 
v___x_1474_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_value_1462_, v_newVal_1458_);
v___y_1466_ = v___x_1474_;
goto v___jp_1465_;
}
v___jp_1465_:
{
if (v___y_1466_ == 0)
{
lean_object* v___x_1467_; 
lean_inc(v_declName_1460_);
lean_dec_ref_known(v_e_1456_, 4);
v___x_1467_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1454_, v_inst_1455_, v_declName_1460_, v_newType_1457_, v_newVal_1458_, v_newBody_1459_, v_nondep_1464_);
return v___x_1467_;
}
else
{
uint8_t v___x_1468_; 
v___x_1468_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1463_, v_newBody_1459_);
if (v___x_1468_ == 0)
{
lean_object* v___x_1469_; 
lean_inc(v_declName_1460_);
lean_dec_ref_known(v_e_1456_, 4);
v___x_1469_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1454_, v_inst_1455_, v_declName_1460_, v_newType_1457_, v_newVal_1458_, v_newBody_1459_, v_nondep_1464_);
return v___x_1469_;
}
else
{
lean_object* v_toApplicative_1470_; lean_object* v_toPure_1471_; lean_object* v___x_1472_; 
lean_dec_ref(v_newBody_1459_);
lean_dec_ref(v_newVal_1458_);
lean_dec_ref(v_newType_1457_);
lean_dec_ref(v_inst_1454_);
v_toApplicative_1470_ = lean_ctor_get(v_inst_1455_, 0);
lean_inc_ref(v_toApplicative_1470_);
lean_dec_ref(v_inst_1455_);
v_toPure_1471_ = lean_ctor_get(v_toApplicative_1470_, 1);
lean_inc(v_toPure_1471_);
lean_dec_ref(v_toApplicative_1470_);
v___x_1472_ = lean_apply_2(v_toPure_1471_, lean_box(0), v_e_1456_);
return v___x_1472_;
}
}
}
}
else
{
lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; 
lean_dec_ref(v_newBody_1459_);
lean_dec_ref(v_newVal_1458_);
lean_dec_ref(v_newType_1457_);
lean_dec_ref(v_e_1456_);
lean_dec_ref(v_inst_1454_);
v___x_1475_ = l_Lean_instInhabitedExpr;
v___x_1476_ = l_instInhabitedOfMonad___redArg(v_inst_1455_, v___x_1475_);
v___x_1477_ = lean_obj_once(&l_Lean_Expr_updateLetS_x21___redArg___closed__2, &l_Lean_Expr_updateLetS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateLetS_x21___redArg___closed__2);
v___x_1478_ = l_panic___redArg(v___x_1476_, v___x_1477_);
lean_dec(v___x_1476_);
return v___x_1478_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___redArg___lam__0(lean_object* v_inst_1479_, lean_object* v_inst_1480_, lean_object* v_a_u2082_1481_, lean_object* v_____do__lift_1482_){
_start:
{
lean_object* v___x_1483_; 
v___x_1483_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1479_, v_inst_1480_, v_____do__lift_1482_, v_a_u2082_1481_);
return v___x_1483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___redArg(lean_object* v_inst_1484_, lean_object* v_inst_1485_, lean_object* v_f_1486_, lean_object* v_a_u2081_1487_, lean_object* v_a_u2082_1488_){
_start:
{
lean_object* v_toBind_1489_; lean_object* v___f_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; 
v_toBind_1489_ = lean_ctor_get(v_inst_1485_, 1);
lean_inc(v_toBind_1489_);
lean_inc_ref(v_inst_1485_);
lean_inc_ref(v_inst_1484_);
v___f_1490_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2082___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1490_, 0, v_inst_1484_);
lean_closure_set(v___f_1490_, 1, v_inst_1485_);
lean_closure_set(v___f_1490_, 2, v_a_u2082_1488_);
v___x_1491_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1484_, v_inst_1485_, v_f_1486_, v_a_u2081_1487_);
v___x_1492_ = lean_apply_4(v_toBind_1489_, lean_box(0), lean_box(0), v___x_1491_, v___f_1490_);
return v___x_1492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082(lean_object* v_m_1493_, lean_object* v_inst_1494_, lean_object* v_inst_1495_, lean_object* v_f_1496_, lean_object* v_a_u2081_1497_, lean_object* v_a_u2082_1498_){
_start:
{
lean_object* v___x_1499_; 
v___x_1499_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___redArg(v_inst_1494_, v_inst_1495_, v_f_1496_, v_a_u2081_1497_, v_a_u2082_1498_);
return v___x_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___redArg___lam__0(lean_object* v_inst_1500_, lean_object* v_inst_1501_, lean_object* v_a_u2083_1502_, lean_object* v_____do__lift_1503_){
_start:
{
lean_object* v___x_1504_; 
v___x_1504_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1500_, v_inst_1501_, v_____do__lift_1503_, v_a_u2083_1502_);
return v___x_1504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___redArg(lean_object* v_inst_1505_, lean_object* v_inst_1506_, lean_object* v_f_1507_, lean_object* v_a_u2081_1508_, lean_object* v_a_u2082_1509_, lean_object* v_a_u2083_1510_){
_start:
{
lean_object* v_toBind_1511_; lean_object* v___f_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; 
v_toBind_1511_ = lean_ctor_get(v_inst_1506_, 1);
lean_inc(v_toBind_1511_);
lean_inc_ref(v_inst_1506_);
lean_inc_ref(v_inst_1505_);
v___f_1512_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2083___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1512_, 0, v_inst_1505_);
lean_closure_set(v___f_1512_, 1, v_inst_1506_);
lean_closure_set(v___f_1512_, 2, v_a_u2083_1510_);
v___x_1513_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___redArg(v_inst_1505_, v_inst_1506_, v_f_1507_, v_a_u2081_1508_, v_a_u2082_1509_);
v___x_1514_ = lean_apply_4(v_toBind_1511_, lean_box(0), lean_box(0), v___x_1513_, v___f_1512_);
return v___x_1514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083(lean_object* v_m_1515_, lean_object* v_inst_1516_, lean_object* v_inst_1517_, lean_object* v_f_1518_, lean_object* v_a_u2081_1519_, lean_object* v_a_u2082_1520_, lean_object* v_a_u2083_1521_){
_start:
{
lean_object* v___x_1522_; 
v___x_1522_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___redArg(v_inst_1516_, v_inst_1517_, v_f_1518_, v_a_u2081_1519_, v_a_u2082_1520_, v_a_u2083_1521_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___redArg___lam__0(lean_object* v_inst_1523_, lean_object* v_inst_1524_, lean_object* v_a_u2084_1525_, lean_object* v_____do__lift_1526_){
_start:
{
lean_object* v___x_1527_; 
v___x_1527_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1523_, v_inst_1524_, v_____do__lift_1526_, v_a_u2084_1525_);
return v___x_1527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___redArg(lean_object* v_inst_1528_, lean_object* v_inst_1529_, lean_object* v_f_1530_, lean_object* v_a_u2081_1531_, lean_object* v_a_u2082_1532_, lean_object* v_a_u2083_1533_, lean_object* v_a_u2084_1534_){
_start:
{
lean_object* v_toBind_1535_; lean_object* v___f_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; 
v_toBind_1535_ = lean_ctor_get(v_inst_1529_, 1);
lean_inc(v_toBind_1535_);
lean_inc_ref(v_inst_1529_);
lean_inc_ref(v_inst_1528_);
v___f_1536_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2084___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1536_, 0, v_inst_1528_);
lean_closure_set(v___f_1536_, 1, v_inst_1529_);
lean_closure_set(v___f_1536_, 2, v_a_u2084_1534_);
v___x_1537_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___redArg(v_inst_1528_, v_inst_1529_, v_f_1530_, v_a_u2081_1531_, v_a_u2082_1532_, v_a_u2083_1533_);
v___x_1538_ = lean_apply_4(v_toBind_1535_, lean_box(0), lean_box(0), v___x_1537_, v___f_1536_);
return v___x_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084(lean_object* v_m_1539_, lean_object* v_inst_1540_, lean_object* v_inst_1541_, lean_object* v_f_1542_, lean_object* v_a_u2081_1543_, lean_object* v_a_u2082_1544_, lean_object* v_a_u2083_1545_, lean_object* v_a_u2084_1546_){
_start:
{
lean_object* v___x_1547_; 
v___x_1547_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___redArg(v_inst_1540_, v_inst_1541_, v_f_1542_, v_a_u2081_1543_, v_a_u2082_1544_, v_a_u2083_1545_, v_a_u2084_1546_);
return v___x_1547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2085___redArg___lam__0(lean_object* v_inst_1548_, lean_object* v_inst_1549_, lean_object* v_a_u2085_1550_, lean_object* v_____do__lift_1551_){
_start:
{
lean_object* v___x_1552_; 
v___x_1552_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1548_, v_inst_1549_, v_____do__lift_1551_, v_a_u2085_1550_);
return v___x_1552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2085___redArg(lean_object* v_inst_1553_, lean_object* v_inst_1554_, lean_object* v_f_1555_, lean_object* v_a_u2081_1556_, lean_object* v_a_u2082_1557_, lean_object* v_a_u2083_1558_, lean_object* v_a_u2084_1559_, lean_object* v_a_u2085_1560_){
_start:
{
lean_object* v_toBind_1561_; lean_object* v___f_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; 
v_toBind_1561_ = lean_ctor_get(v_inst_1554_, 1);
lean_inc(v_toBind_1561_);
lean_inc_ref(v_inst_1554_);
lean_inc_ref(v_inst_1553_);
v___f_1562_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2085___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1562_, 0, v_inst_1553_);
lean_closure_set(v___f_1562_, 1, v_inst_1554_);
lean_closure_set(v___f_1562_, 2, v_a_u2085_1560_);
v___x_1563_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___redArg(v_inst_1553_, v_inst_1554_, v_f_1555_, v_a_u2081_1556_, v_a_u2082_1557_, v_a_u2083_1558_, v_a_u2084_1559_);
v___x_1564_ = lean_apply_4(v_toBind_1561_, lean_box(0), lean_box(0), v___x_1563_, v___f_1562_);
return v___x_1564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2085(lean_object* v_m_1565_, lean_object* v_inst_1566_, lean_object* v_inst_1567_, lean_object* v_f_1568_, lean_object* v_a_u2081_1569_, lean_object* v_a_u2082_1570_, lean_object* v_a_u2083_1571_, lean_object* v_a_u2084_1572_, lean_object* v_a_u2085_1573_){
_start:
{
lean_object* v___x_1574_; 
v___x_1574_ = l_Lean_Meta_Sym_Internal_mkAppS_u2085___redArg(v_inst_1566_, v_inst_1567_, v_f_1568_, v_a_u2081_1569_, v_a_u2082_1570_, v_a_u2083_1571_, v_a_u2084_1572_, v_a_u2085_1573_);
return v___x_1574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2086___redArg___lam__0(lean_object* v_inst_1575_, lean_object* v_inst_1576_, lean_object* v_a_u2086_1577_, lean_object* v_____do__lift_1578_){
_start:
{
lean_object* v___x_1579_; 
v___x_1579_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1575_, v_inst_1576_, v_____do__lift_1578_, v_a_u2086_1577_);
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2086___redArg(lean_object* v_inst_1580_, lean_object* v_inst_1581_, lean_object* v_f_1582_, lean_object* v_a_u2081_1583_, lean_object* v_a_u2082_1584_, lean_object* v_a_u2083_1585_, lean_object* v_a_u2084_1586_, lean_object* v_a_u2085_1587_, lean_object* v_a_u2086_1588_){
_start:
{
lean_object* v_toBind_1589_; lean_object* v___f_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; 
v_toBind_1589_ = lean_ctor_get(v_inst_1581_, 1);
lean_inc(v_toBind_1589_);
lean_inc_ref(v_inst_1581_);
lean_inc_ref(v_inst_1580_);
v___f_1590_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2086___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1590_, 0, v_inst_1580_);
lean_closure_set(v___f_1590_, 1, v_inst_1581_);
lean_closure_set(v___f_1590_, 2, v_a_u2086_1588_);
v___x_1591_ = l_Lean_Meta_Sym_Internal_mkAppS_u2085___redArg(v_inst_1580_, v_inst_1581_, v_f_1582_, v_a_u2081_1583_, v_a_u2082_1584_, v_a_u2083_1585_, v_a_u2084_1586_, v_a_u2085_1587_);
v___x_1592_ = lean_apply_4(v_toBind_1589_, lean_box(0), lean_box(0), v___x_1591_, v___f_1590_);
return v___x_1592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2086(lean_object* v_m_1593_, lean_object* v_inst_1594_, lean_object* v_inst_1595_, lean_object* v_f_1596_, lean_object* v_a_u2081_1597_, lean_object* v_a_u2082_1598_, lean_object* v_a_u2083_1599_, lean_object* v_a_u2084_1600_, lean_object* v_a_u2085_1601_, lean_object* v_a_u2086_1602_){
_start:
{
lean_object* v___x_1603_; 
v___x_1603_ = l_Lean_Meta_Sym_Internal_mkAppS_u2086___redArg(v_inst_1594_, v_inst_1595_, v_f_1596_, v_a_u2081_1597_, v_a_u2082_1598_, v_a_u2083_1599_, v_a_u2084_1600_, v_a_u2085_1601_, v_a_u2086_1602_);
return v___x_1603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2087___redArg___lam__0(lean_object* v_inst_1604_, lean_object* v_inst_1605_, lean_object* v_a_u2087_1606_, lean_object* v_____do__lift_1607_){
_start:
{
lean_object* v___x_1608_; 
v___x_1608_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1604_, v_inst_1605_, v_____do__lift_1607_, v_a_u2087_1606_);
return v___x_1608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2087___redArg(lean_object* v_inst_1609_, lean_object* v_inst_1610_, lean_object* v_f_1611_, lean_object* v_a_u2081_1612_, lean_object* v_a_u2082_1613_, lean_object* v_a_u2083_1614_, lean_object* v_a_u2084_1615_, lean_object* v_a_u2085_1616_, lean_object* v_a_u2086_1617_, lean_object* v_a_u2087_1618_){
_start:
{
lean_object* v_toBind_1619_; lean_object* v___f_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; 
v_toBind_1619_ = lean_ctor_get(v_inst_1610_, 1);
lean_inc(v_toBind_1619_);
lean_inc_ref(v_inst_1610_);
lean_inc_ref(v_inst_1609_);
v___f_1620_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2087___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1620_, 0, v_inst_1609_);
lean_closure_set(v___f_1620_, 1, v_inst_1610_);
lean_closure_set(v___f_1620_, 2, v_a_u2087_1618_);
v___x_1621_ = l_Lean_Meta_Sym_Internal_mkAppS_u2086___redArg(v_inst_1609_, v_inst_1610_, v_f_1611_, v_a_u2081_1612_, v_a_u2082_1613_, v_a_u2083_1614_, v_a_u2084_1615_, v_a_u2085_1616_, v_a_u2086_1617_);
v___x_1622_ = lean_apply_4(v_toBind_1619_, lean_box(0), lean_box(0), v___x_1621_, v___f_1620_);
return v___x_1622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2087(lean_object* v_m_1623_, lean_object* v_inst_1624_, lean_object* v_inst_1625_, lean_object* v_f_1626_, lean_object* v_a_u2081_1627_, lean_object* v_a_u2082_1628_, lean_object* v_a_u2083_1629_, lean_object* v_a_u2084_1630_, lean_object* v_a_u2085_1631_, lean_object* v_a_u2086_1632_, lean_object* v_a_u2087_1633_){
_start:
{
lean_object* v___x_1634_; 
v___x_1634_ = l_Lean_Meta_Sym_Internal_mkAppS_u2087___redArg(v_inst_1624_, v_inst_1625_, v_f_1626_, v_a_u2081_1627_, v_a_u2082_1628_, v_a_u2083_1629_, v_a_u2084_1630_, v_a_u2085_1631_, v_a_u2086_1632_, v_a_u2087_1633_);
return v___x_1634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2088___redArg___lam__0(lean_object* v_inst_1635_, lean_object* v_inst_1636_, lean_object* v_a_u2088_1637_, lean_object* v_____do__lift_1638_){
_start:
{
lean_object* v___x_1639_; 
v___x_1639_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1635_, v_inst_1636_, v_____do__lift_1638_, v_a_u2088_1637_);
return v___x_1639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2088___redArg(lean_object* v_inst_1640_, lean_object* v_inst_1641_, lean_object* v_f_1642_, lean_object* v_a_u2081_1643_, lean_object* v_a_u2082_1644_, lean_object* v_a_u2083_1645_, lean_object* v_a_u2084_1646_, lean_object* v_a_u2085_1647_, lean_object* v_a_u2086_1648_, lean_object* v_a_u2087_1649_, lean_object* v_a_u2088_1650_){
_start:
{
lean_object* v_toBind_1651_; lean_object* v___f_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; 
v_toBind_1651_ = lean_ctor_get(v_inst_1641_, 1);
lean_inc(v_toBind_1651_);
lean_inc_ref(v_inst_1641_);
lean_inc_ref(v_inst_1640_);
v___f_1652_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2088___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1652_, 0, v_inst_1640_);
lean_closure_set(v___f_1652_, 1, v_inst_1641_);
lean_closure_set(v___f_1652_, 2, v_a_u2088_1650_);
v___x_1653_ = l_Lean_Meta_Sym_Internal_mkAppS_u2087___redArg(v_inst_1640_, v_inst_1641_, v_f_1642_, v_a_u2081_1643_, v_a_u2082_1644_, v_a_u2083_1645_, v_a_u2084_1646_, v_a_u2085_1647_, v_a_u2086_1648_, v_a_u2087_1649_);
v___x_1654_ = lean_apply_4(v_toBind_1651_, lean_box(0), lean_box(0), v___x_1653_, v___f_1652_);
return v___x_1654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2088(lean_object* v_m_1655_, lean_object* v_inst_1656_, lean_object* v_inst_1657_, lean_object* v_f_1658_, lean_object* v_a_u2081_1659_, lean_object* v_a_u2082_1660_, lean_object* v_a_u2083_1661_, lean_object* v_a_u2084_1662_, lean_object* v_a_u2085_1663_, lean_object* v_a_u2086_1664_, lean_object* v_a_u2087_1665_, lean_object* v_a_u2088_1666_){
_start:
{
lean_object* v___x_1667_; 
v___x_1667_ = l_Lean_Meta_Sym_Internal_mkAppS_u2088___redArg(v_inst_1656_, v_inst_1657_, v_f_1658_, v_a_u2081_1659_, v_a_u2082_1660_, v_a_u2083_1661_, v_a_u2084_1662_, v_a_u2085_1663_, v_a_u2086_1664_, v_a_u2087_1665_, v_a_u2088_1666_);
return v___x_1667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2089___redArg___lam__0(lean_object* v_inst_1668_, lean_object* v_inst_1669_, lean_object* v_a_u2089_1670_, lean_object* v_____do__lift_1671_){
_start:
{
lean_object* v___x_1672_; 
v___x_1672_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1668_, v_inst_1669_, v_____do__lift_1671_, v_a_u2089_1670_);
return v___x_1672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2089___redArg(lean_object* v_inst_1673_, lean_object* v_inst_1674_, lean_object* v_f_1675_, lean_object* v_a_u2081_1676_, lean_object* v_a_u2082_1677_, lean_object* v_a_u2083_1678_, lean_object* v_a_u2084_1679_, lean_object* v_a_u2085_1680_, lean_object* v_a_u2086_1681_, lean_object* v_a_u2087_1682_, lean_object* v_a_u2088_1683_, lean_object* v_a_u2089_1684_){
_start:
{
lean_object* v_toBind_1685_; lean_object* v___f_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; 
v_toBind_1685_ = lean_ctor_get(v_inst_1674_, 1);
lean_inc(v_toBind_1685_);
lean_inc_ref(v_inst_1674_);
lean_inc_ref(v_inst_1673_);
v___f_1686_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2089___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1686_, 0, v_inst_1673_);
lean_closure_set(v___f_1686_, 1, v_inst_1674_);
lean_closure_set(v___f_1686_, 2, v_a_u2089_1684_);
v___x_1687_ = l_Lean_Meta_Sym_Internal_mkAppS_u2088___redArg(v_inst_1673_, v_inst_1674_, v_f_1675_, v_a_u2081_1676_, v_a_u2082_1677_, v_a_u2083_1678_, v_a_u2084_1679_, v_a_u2085_1680_, v_a_u2086_1681_, v_a_u2087_1682_, v_a_u2088_1683_);
v___x_1688_ = lean_apply_4(v_toBind_1685_, lean_box(0), lean_box(0), v___x_1687_, v___f_1686_);
return v___x_1688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2089(lean_object* v_m_1689_, lean_object* v_inst_1690_, lean_object* v_inst_1691_, lean_object* v_f_1692_, lean_object* v_a_u2081_1693_, lean_object* v_a_u2082_1694_, lean_object* v_a_u2083_1695_, lean_object* v_a_u2084_1696_, lean_object* v_a_u2085_1697_, lean_object* v_a_u2086_1698_, lean_object* v_a_u2087_1699_, lean_object* v_a_u2088_1700_, lean_object* v_a_u2089_1701_){
_start:
{
lean_object* v___x_1702_; 
v___x_1702_ = l_Lean_Meta_Sym_Internal_mkAppS_u2089___redArg(v_inst_1690_, v_inst_1691_, v_f_1692_, v_a_u2081_1693_, v_a_u2082_1694_, v_a_u2083_1695_, v_a_u2084_1696_, v_a_u2085_1697_, v_a_u2086_1698_, v_a_u2087_1699_, v_a_u2088_1700_, v_a_u2089_1701_);
return v___x_1702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2080___redArg___lam__0(lean_object* v_inst_1703_, lean_object* v_inst_1704_, lean_object* v_a_u2081_u2080_1705_, lean_object* v_____do__lift_1706_){
_start:
{
lean_object* v___x_1707_; 
v___x_1707_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1703_, v_inst_1704_, v_____do__lift_1706_, v_a_u2081_u2080_1705_);
return v___x_1707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2080___redArg(lean_object* v_inst_1708_, lean_object* v_inst_1709_, lean_object* v_f_1710_, lean_object* v_a_u2081_1711_, lean_object* v_a_u2082_1712_, lean_object* v_a_u2083_1713_, lean_object* v_a_u2084_1714_, lean_object* v_a_u2085_1715_, lean_object* v_a_u2086_1716_, lean_object* v_a_u2087_1717_, lean_object* v_a_u2088_1718_, lean_object* v_a_u2089_1719_, lean_object* v_a_u2081_u2080_1720_){
_start:
{
lean_object* v_toBind_1721_; lean_object* v___f_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; 
v_toBind_1721_ = lean_ctor_get(v_inst_1709_, 1);
lean_inc(v_toBind_1721_);
lean_inc_ref(v_inst_1709_);
lean_inc_ref(v_inst_1708_);
v___f_1722_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2080___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1722_, 0, v_inst_1708_);
lean_closure_set(v___f_1722_, 1, v_inst_1709_);
lean_closure_set(v___f_1722_, 2, v_a_u2081_u2080_1720_);
v___x_1723_ = l_Lean_Meta_Sym_Internal_mkAppS_u2089___redArg(v_inst_1708_, v_inst_1709_, v_f_1710_, v_a_u2081_1711_, v_a_u2082_1712_, v_a_u2083_1713_, v_a_u2084_1714_, v_a_u2085_1715_, v_a_u2086_1716_, v_a_u2087_1717_, v_a_u2088_1718_, v_a_u2089_1719_);
v___x_1724_ = lean_apply_4(v_toBind_1721_, lean_box(0), lean_box(0), v___x_1723_, v___f_1722_);
return v___x_1724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2080(lean_object* v_m_1725_, lean_object* v_inst_1726_, lean_object* v_inst_1727_, lean_object* v_f_1728_, lean_object* v_a_u2081_1729_, lean_object* v_a_u2082_1730_, lean_object* v_a_u2083_1731_, lean_object* v_a_u2084_1732_, lean_object* v_a_u2085_1733_, lean_object* v_a_u2086_1734_, lean_object* v_a_u2087_1735_, lean_object* v_a_u2088_1736_, lean_object* v_a_u2089_1737_, lean_object* v_a_u2081_u2080_1738_){
_start:
{
lean_object* v___x_1739_; 
v___x_1739_ = l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2080___redArg(v_inst_1726_, v_inst_1727_, v_f_1728_, v_a_u2081_1729_, v_a_u2082_1730_, v_a_u2083_1731_, v_a_u2084_1732_, v_a_u2085_1733_, v_a_u2086_1734_, v_a_u2087_1735_, v_a_u2088_1736_, v_a_u2089_1737_, v_a_u2081_u2080_1738_);
return v___x_1739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2081___redArg___lam__0(lean_object* v_inst_1740_, lean_object* v_inst_1741_, lean_object* v_a_u2081_u2081_1742_, lean_object* v_____do__lift_1743_){
_start:
{
lean_object* v___x_1744_; 
v___x_1744_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1740_, v_inst_1741_, v_____do__lift_1743_, v_a_u2081_u2081_1742_);
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2081___redArg(lean_object* v_inst_1745_, lean_object* v_inst_1746_, lean_object* v_f_1747_, lean_object* v_a_u2081_1748_, lean_object* v_a_u2082_1749_, lean_object* v_a_u2083_1750_, lean_object* v_a_u2084_1751_, lean_object* v_a_u2085_1752_, lean_object* v_a_u2086_1753_, lean_object* v_a_u2087_1754_, lean_object* v_a_u2088_1755_, lean_object* v_a_u2089_1756_, lean_object* v_a_u2081_u2080_1757_, lean_object* v_a_u2081_u2081_1758_){
_start:
{
lean_object* v_toBind_1759_; lean_object* v___f_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; 
v_toBind_1759_ = lean_ctor_get(v_inst_1746_, 1);
lean_inc(v_toBind_1759_);
lean_inc_ref(v_inst_1746_);
lean_inc_ref(v_inst_1745_);
v___f_1760_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2081___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1760_, 0, v_inst_1745_);
lean_closure_set(v___f_1760_, 1, v_inst_1746_);
lean_closure_set(v___f_1760_, 2, v_a_u2081_u2081_1758_);
v___x_1761_ = l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2080___redArg(v_inst_1745_, v_inst_1746_, v_f_1747_, v_a_u2081_1748_, v_a_u2082_1749_, v_a_u2083_1750_, v_a_u2084_1751_, v_a_u2085_1752_, v_a_u2086_1753_, v_a_u2087_1754_, v_a_u2088_1755_, v_a_u2089_1756_, v_a_u2081_u2080_1757_);
v___x_1762_ = lean_apply_4(v_toBind_1759_, lean_box(0), lean_box(0), v___x_1761_, v___f_1760_);
return v___x_1762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2081(lean_object* v_m_1763_, lean_object* v_inst_1764_, lean_object* v_inst_1765_, lean_object* v_f_1766_, lean_object* v_a_u2081_1767_, lean_object* v_a_u2082_1768_, lean_object* v_a_u2083_1769_, lean_object* v_a_u2084_1770_, lean_object* v_a_u2085_1771_, lean_object* v_a_u2086_1772_, lean_object* v_a_u2087_1773_, lean_object* v_a_u2088_1774_, lean_object* v_a_u2089_1775_, lean_object* v_a_u2081_u2080_1776_, lean_object* v_a_u2081_u2081_1777_){
_start:
{
lean_object* v___x_1778_; 
v___x_1778_ = l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2081___redArg(v_inst_1764_, v_inst_1765_, v_f_1766_, v_a_u2081_1767_, v_a_u2082_1768_, v_a_u2083_1769_, v_a_u2084_1770_, v_a_u2085_1771_, v_a_u2086_1772_, v_a_u2087_1773_, v_a_u2088_1774_, v_a_u2089_1775_, v_a_u2081_u2080_1776_, v_a_u2081_u2081_1777_);
return v___x_1778_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg___lam__0___boxed(lean_object* v_i_1779_, lean_object* v_inst_1780_, lean_object* v_inst_1781_, lean_object* v_args_1782_, lean_object* v_endIdx_1783_, lean_object* v_____do__lift_1784_){
_start:
{
lean_object* v_res_1785_; 
v_res_1785_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg___lam__0(v_i_1779_, v_inst_1780_, v_inst_1781_, v_args_1782_, v_endIdx_1783_, v_____do__lift_1784_);
lean_dec(v_i_1779_);
return v_res_1785_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg(lean_object* v_inst_1786_, lean_object* v_inst_1787_, lean_object* v_args_1788_, lean_object* v_endIdx_1789_, lean_object* v_b_1790_, lean_object* v_i_1791_){
_start:
{
uint8_t v___x_1792_; 
v___x_1792_ = lean_nat_dec_le(v_endIdx_1789_, v_i_1791_);
if (v___x_1792_ == 0)
{
lean_object* v_toBind_1793_; lean_object* v___f_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; 
v_toBind_1793_ = lean_ctor_get(v_inst_1787_, 1);
lean_inc(v_toBind_1793_);
lean_inc_ref(v_args_1788_);
lean_inc_ref(v_inst_1787_);
lean_inc_ref(v_inst_1786_);
lean_inc(v_i_1791_);
v___f_1794_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1794_, 0, v_i_1791_);
lean_closure_set(v___f_1794_, 1, v_inst_1786_);
lean_closure_set(v___f_1794_, 2, v_inst_1787_);
lean_closure_set(v___f_1794_, 3, v_args_1788_);
lean_closure_set(v___f_1794_, 4, v_endIdx_1789_);
v___x_1795_ = l_Lean_instInhabitedExpr;
v___x_1796_ = lean_array_get(v___x_1795_, v_args_1788_, v_i_1791_);
lean_dec(v_i_1791_);
lean_dec_ref(v_args_1788_);
v___x_1797_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1786_, v_inst_1787_, v_b_1790_, v___x_1796_);
v___x_1798_ = lean_apply_4(v_toBind_1793_, lean_box(0), lean_box(0), v___x_1797_, v___f_1794_);
return v___x_1798_;
}
else
{
lean_object* v_toApplicative_1799_; lean_object* v_toPure_1800_; lean_object* v___x_1801_; 
lean_dec(v_i_1791_);
lean_dec(v_endIdx_1789_);
lean_dec_ref(v_args_1788_);
lean_dec_ref(v_inst_1786_);
v_toApplicative_1799_ = lean_ctor_get(v_inst_1787_, 0);
lean_inc_ref(v_toApplicative_1799_);
lean_dec_ref(v_inst_1787_);
v_toPure_1800_ = lean_ctor_get(v_toApplicative_1799_, 1);
lean_inc(v_toPure_1800_);
lean_dec_ref(v_toApplicative_1799_);
v___x_1801_ = lean_apply_2(v_toPure_1800_, lean_box(0), v_b_1790_);
return v___x_1801_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg___lam__0(lean_object* v_i_1802_, lean_object* v_inst_1803_, lean_object* v_inst_1804_, lean_object* v_args_1805_, lean_object* v_endIdx_1806_, lean_object* v_____do__lift_1807_){
_start:
{
lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1808_ = lean_unsigned_to_nat(1u);
v___x_1809_ = lean_nat_add(v_i_1802_, v___x_1808_);
v___x_1810_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg(v_inst_1803_, v_inst_1804_, v_args_1805_, v_endIdx_1806_, v_____do__lift_1807_, v___x_1809_);
return v___x_1810_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go(lean_object* v_m_1811_, lean_object* v_inst_1812_, lean_object* v_inst_1813_, lean_object* v_args_1814_, lean_object* v_endIdx_1815_, lean_object* v_b_1816_, lean_object* v_i_1817_){
_start:
{
lean_object* v___x_1818_; 
v___x_1818_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg(v_inst_1812_, v_inst_1813_, v_args_1814_, v_endIdx_1815_, v_b_1816_, v_i_1817_);
return v___x_1818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRangeS___redArg(lean_object* v_inst_1819_, lean_object* v_inst_1820_, lean_object* v_f_1821_, lean_object* v_beginIdx_1822_, lean_object* v_endIdx_1823_, lean_object* v_args_1824_){
_start:
{
lean_object* v___x_1825_; 
v___x_1825_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg(v_inst_1819_, v_inst_1820_, v_args_1824_, v_endIdx_1823_, v_f_1821_, v_beginIdx_1822_);
return v___x_1825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRangeS(lean_object* v_m_1826_, lean_object* v_inst_1827_, lean_object* v_inst_1828_, lean_object* v_f_1829_, lean_object* v_beginIdx_1830_, lean_object* v_endIdx_1831_, lean_object* v_args_1832_){
_start:
{
lean_object* v___x_1833_; 
v___x_1833_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg(v_inst_1827_, v_inst_1828_, v_args_1832_, v_endIdx_1831_, v_f_1829_, v_beginIdx_1830_);
return v___x_1833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___redArg(lean_object* v_inst_1834_, lean_object* v_inst_1835_, lean_object* v_f_1836_, lean_object* v_args_1837_){
_start:
{
lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; 
v___x_1838_ = lean_unsigned_to_nat(0u);
v___x_1839_ = lean_array_get_size(v_args_1837_);
v___x_1840_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg(v_inst_1834_, v_inst_1835_, v_args_1837_, v___x_1839_, v_f_1836_, v___x_1838_);
return v___x_1840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS(lean_object* v_m_1841_, lean_object* v_inst_1842_, lean_object* v_inst_1843_, lean_object* v_f_1844_, lean_object* v_args_1845_){
_start:
{
lean_object* v___x_1846_; 
v___x_1846_ = l_Lean_Meta_Sym_Internal_mkAppNS___redArg(v_inst_1842_, v_inst_1843_, v_f_1844_, v_args_1845_);
return v___x_1846_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg___lam__0___boxed(lean_object* v_inst_1847_, lean_object* v_inst_1848_, lean_object* v_revArgs_1849_, lean_object* v_start_1850_, lean_object* v_i_1851_, lean_object* v_____do__lift_1852_){
_start:
{
lean_object* v_res_1853_; 
v_res_1853_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg___lam__0(v_inst_1847_, v_inst_1848_, v_revArgs_1849_, v_start_1850_, v_i_1851_, v_____do__lift_1852_);
lean_dec(v_i_1851_);
return v_res_1853_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg(lean_object* v_inst_1854_, lean_object* v_inst_1855_, lean_object* v_revArgs_1856_, lean_object* v_start_1857_, lean_object* v_b_1858_, lean_object* v_i_1859_){
_start:
{
uint8_t v___x_1860_; 
v___x_1860_ = lean_nat_dec_le(v_i_1859_, v_start_1857_);
if (v___x_1860_ == 0)
{
lean_object* v_toBind_1861_; lean_object* v___x_1862_; lean_object* v_i_1863_; lean_object* v___f_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; 
v_toBind_1861_ = lean_ctor_get(v_inst_1855_, 1);
lean_inc(v_toBind_1861_);
v___x_1862_ = lean_unsigned_to_nat(1u);
v_i_1863_ = lean_nat_sub(v_i_1859_, v___x_1862_);
lean_inc(v_i_1863_);
lean_inc_ref(v_revArgs_1856_);
lean_inc_ref(v_inst_1855_);
lean_inc_ref(v_inst_1854_);
v___f_1864_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1864_, 0, v_inst_1854_);
lean_closure_set(v___f_1864_, 1, v_inst_1855_);
lean_closure_set(v___f_1864_, 2, v_revArgs_1856_);
lean_closure_set(v___f_1864_, 3, v_start_1857_);
lean_closure_set(v___f_1864_, 4, v_i_1863_);
v___x_1865_ = l_Lean_instInhabitedExpr;
v___x_1866_ = lean_array_get(v___x_1865_, v_revArgs_1856_, v_i_1863_);
lean_dec(v_i_1863_);
lean_dec_ref(v_revArgs_1856_);
v___x_1867_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1854_, v_inst_1855_, v_b_1858_, v___x_1866_);
v___x_1868_ = lean_apply_4(v_toBind_1861_, lean_box(0), lean_box(0), v___x_1867_, v___f_1864_);
return v___x_1868_;
}
else
{
lean_object* v_toApplicative_1869_; lean_object* v_toPure_1870_; lean_object* v___x_1871_; 
lean_dec(v_start_1857_);
lean_dec_ref(v_revArgs_1856_);
lean_dec_ref(v_inst_1854_);
v_toApplicative_1869_ = lean_ctor_get(v_inst_1855_, 0);
lean_inc_ref(v_toApplicative_1869_);
lean_dec_ref(v_inst_1855_);
v_toPure_1870_ = lean_ctor_get(v_toApplicative_1869_, 1);
lean_inc(v_toPure_1870_);
lean_dec_ref(v_toApplicative_1869_);
v___x_1871_ = lean_apply_2(v_toPure_1870_, lean_box(0), v_b_1858_);
return v___x_1871_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg___lam__0(lean_object* v_inst_1872_, lean_object* v_inst_1873_, lean_object* v_revArgs_1874_, lean_object* v_start_1875_, lean_object* v_i_1876_, lean_object* v_____do__lift_1877_){
_start:
{
lean_object* v___x_1878_; 
v___x_1878_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg(v_inst_1872_, v_inst_1873_, v_revArgs_1874_, v_start_1875_, v_____do__lift_1877_, v_i_1876_);
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg___boxed(lean_object* v_inst_1879_, lean_object* v_inst_1880_, lean_object* v_revArgs_1881_, lean_object* v_start_1882_, lean_object* v_b_1883_, lean_object* v_i_1884_){
_start:
{
lean_object* v_res_1885_; 
v_res_1885_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg(v_inst_1879_, v_inst_1880_, v_revArgs_1881_, v_start_1882_, v_b_1883_, v_i_1884_);
lean_dec(v_i_1884_);
return v_res_1885_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go(lean_object* v_m_1886_, lean_object* v_inst_1887_, lean_object* v_inst_1888_, lean_object* v_revArgs_1889_, lean_object* v_start_1890_, lean_object* v_b_1891_, lean_object* v_i_1892_){
_start:
{
lean_object* v___x_1893_; 
v___x_1893_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg(v_inst_1887_, v_inst_1888_, v_revArgs_1889_, v_start_1890_, v_b_1891_, v_i_1892_);
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___boxed(lean_object* v_m_1894_, lean_object* v_inst_1895_, lean_object* v_inst_1896_, lean_object* v_revArgs_1897_, lean_object* v_start_1898_, lean_object* v_b_1899_, lean_object* v_i_1900_){
_start:
{
lean_object* v_res_1901_; 
v_res_1901_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go(v_m_1894_, v_inst_1895_, v_inst_1896_, v_revArgs_1897_, v_start_1898_, v_b_1899_, v_i_1900_);
lean_dec(v_i_1900_);
return v_res_1901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevRangeS___redArg(lean_object* v_inst_1902_, lean_object* v_inst_1903_, lean_object* v_f_1904_, lean_object* v_beginIdx_1905_, lean_object* v_endIdx_1906_, lean_object* v_revArgs_1907_){
_start:
{
lean_object* v___x_1908_; 
v___x_1908_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg(v_inst_1902_, v_inst_1903_, v_revArgs_1907_, v_beginIdx_1905_, v_f_1904_, v_endIdx_1906_);
return v___x_1908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevRangeS___redArg___boxed(lean_object* v_inst_1909_, lean_object* v_inst_1910_, lean_object* v_f_1911_, lean_object* v_beginIdx_1912_, lean_object* v_endIdx_1913_, lean_object* v_revArgs_1914_){
_start:
{
lean_object* v_res_1915_; 
v_res_1915_ = l_Lean_Meta_Sym_Internal_mkAppRevRangeS___redArg(v_inst_1909_, v_inst_1910_, v_f_1911_, v_beginIdx_1912_, v_endIdx_1913_, v_revArgs_1914_);
lean_dec(v_endIdx_1913_);
return v_res_1915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevRangeS(lean_object* v_m_1916_, lean_object* v_inst_1917_, lean_object* v_inst_1918_, lean_object* v_f_1919_, lean_object* v_beginIdx_1920_, lean_object* v_endIdx_1921_, lean_object* v_revArgs_1922_){
_start:
{
lean_object* v___x_1923_; 
v___x_1923_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg(v_inst_1917_, v_inst_1918_, v_revArgs_1922_, v_beginIdx_1920_, v_f_1919_, v_endIdx_1921_);
return v___x_1923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevRangeS___boxed(lean_object* v_m_1924_, lean_object* v_inst_1925_, lean_object* v_inst_1926_, lean_object* v_f_1927_, lean_object* v_beginIdx_1928_, lean_object* v_endIdx_1929_, lean_object* v_revArgs_1930_){
_start:
{
lean_object* v_res_1931_; 
v_res_1931_ = l_Lean_Meta_Sym_Internal_mkAppRevRangeS(v_m_1924_, v_inst_1925_, v_inst_1926_, v_f_1927_, v_beginIdx_1928_, v_endIdx_1929_, v_revArgs_1930_);
lean_dec(v_endIdx_1929_);
return v_res_1931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevS___redArg(lean_object* v_inst_1932_, lean_object* v_inst_1933_, lean_object* v_f_1934_, lean_object* v_revArgs_1935_){
_start:
{
lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; 
v___x_1936_ = lean_unsigned_to_nat(0u);
v___x_1937_ = lean_array_get_size(v_revArgs_1935_);
v___x_1938_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg(v_inst_1932_, v_inst_1933_, v_revArgs_1935_, v___x_1936_, v_f_1934_, v___x_1937_);
return v___x_1938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevS(lean_object* v_m_1939_, lean_object* v_inst_1940_, lean_object* v_inst_1941_, lean_object* v_f_1942_, lean_object* v_revArgs_1943_){
_start:
{
lean_object* v___x_1944_; 
v___x_1944_ = l_Lean_Meta_Sym_Internal_mkAppRevS___redArg(v_inst_1940_, v_inst_1941_, v_f_1942_, v_revArgs_1943_);
return v___x_1944_;
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
