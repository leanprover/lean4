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
static lean_object* _init_l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__0(void){
_start:
{
lean_object* v___x_442_; 
v___x_442_ = l_Lean_Meta_Sym_instInhabitedSymM(lean_box(0));
return v___x_442_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__3(void){
_start:
{
lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_445_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2));
v___x_446_ = lean_unsigned_to_nat(16u);
v___x_447_ = lean_unsigned_to_nat(62u);
v___x_448_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__1));
v___x_449_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_450_ = l_mkPanicMessageWithDecl(v___x_449_, v___x_448_, v___x_447_, v___x_446_, v___x_445_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM___redArg(lean_object* v_k_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; uint8_t v_debug_461_; lean_object* v_env_462_; lean_object* v___x_463_; lean_object* v___x_464_; uint8_t v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_459_ = lean_st_ref_get(v_a_453_);
v___x_460_ = lean_st_ref_get(v_a_457_);
v_debug_461_ = lean_ctor_get_uint8(v___x_459_, sizeof(void*)*10);
lean_dec(v___x_459_);
v_env_462_ = lean_ctor_get(v___x_460_, 0);
lean_inc_ref(v_env_462_);
lean_dec(v___x_460_);
v___x_463_ = lean_box(v_debug_461_);
v___x_464_ = lean_apply_1(v_k_451_, v___x_463_);
v___x_465_ = 0;
v___x_466_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_466_, 0, v_env_462_);
lean_ctor_set_uint8(v___x_466_, sizeof(void*)*1, v___x_465_);
lean_ctor_set_uint8(v___x_466_, sizeof(void*)*1 + 1, v___x_465_);
v___x_467_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___x_464_, v___x_466_, v_a_453_);
if (lean_obj_tag(v___x_467_) == 0)
{
lean_object* v_a_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_480_; 
v_a_468_ = lean_ctor_get(v___x_467_, 0);
v_isSharedCheck_480_ = !lean_is_exclusive(v___x_467_);
if (v_isSharedCheck_480_ == 0)
{
v___x_470_ = v___x_467_;
v_isShared_471_ = v_isSharedCheck_480_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_a_468_);
lean_dec(v___x_467_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_480_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
if (lean_obj_tag(v_a_468_) == 0)
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_1305__overap_474_; lean_object* v___x_475_; 
lean_dec_ref_known(v_a_468_, 1);
lean_del_object(v___x_470_);
v___x_472_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__0, &l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__0_once, _init_l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__0);
v___x_473_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__3, &l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__3_once, _init_l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__3);
v___x_1305__overap_474_ = l_panic___redArg(v___x_472_, v___x_473_);
lean_inc(v_a_457_);
lean_inc_ref(v_a_456_);
lean_inc(v_a_455_);
lean_inc_ref(v_a_454_);
lean_inc(v_a_453_);
lean_inc_ref(v_a_452_);
v___x_475_ = lean_apply_7(v___x_1305__overap_474_, v_a_452_, v_a_453_, v_a_454_, v_a_455_, v_a_456_, v_a_457_, lean_box(0));
return v___x_475_;
}
else
{
lean_object* v_a_476_; lean_object* v___x_478_; 
v_a_476_ = lean_ctor_get(v_a_468_, 0);
lean_inc(v_a_476_);
lean_dec_ref_known(v_a_468_, 1);
if (v_isShared_471_ == 0)
{
lean_ctor_set(v___x_470_, 0, v_a_476_);
v___x_478_ = v___x_470_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v_a_476_);
v___x_478_ = v_reuseFailAlloc_479_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
return v___x_478_;
}
}
}
}
else
{
lean_object* v_a_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_488_; 
v_a_481_ = lean_ctor_get(v___x_467_, 0);
v_isSharedCheck_488_ = !lean_is_exclusive(v___x_467_);
if (v_isSharedCheck_488_ == 0)
{
v___x_483_ = v___x_467_;
v_isShared_484_ = v_isSharedCheck_488_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_a_481_);
lean_dec(v___x_467_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_488_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_486_; 
if (v_isShared_484_ == 0)
{
v___x_486_ = v___x_483_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v_a_481_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
return v___x_486_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___boxed(lean_object* v_k_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l_Lean_Meta_Sym_Internal_liftBuilderM___redArg(v_k_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_, v_a_495_);
lean_dec(v_a_495_);
lean_dec_ref(v_a_494_);
lean_dec(v_a_493_);
lean_dec_ref(v_a_492_);
lean_dec(v_a_491_);
lean_dec_ref(v_a_490_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM(lean_object* v_00_u03b1_498_, lean_object* v_k_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_){
_start:
{
lean_object* v___x_507_; lean_object* v___x_508_; uint8_t v_debug_509_; lean_object* v_env_510_; lean_object* v___x_511_; lean_object* v___x_512_; uint8_t v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_507_ = lean_st_ref_get(v_a_501_);
v___x_508_ = lean_st_ref_get(v_a_505_);
v_debug_509_ = lean_ctor_get_uint8(v___x_507_, sizeof(void*)*10);
lean_dec(v___x_507_);
v_env_510_ = lean_ctor_get(v___x_508_, 0);
lean_inc_ref(v_env_510_);
lean_dec(v___x_508_);
v___x_511_ = lean_box(v_debug_509_);
v___x_512_ = lean_apply_1(v_k_499_, v___x_511_);
v___x_513_ = 0;
v___x_514_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_514_, 0, v_env_510_);
lean_ctor_set_uint8(v___x_514_, sizeof(void*)*1, v___x_513_);
lean_ctor_set_uint8(v___x_514_, sizeof(void*)*1 + 1, v___x_513_);
v___x_515_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___x_512_, v___x_514_, v_a_501_);
if (lean_obj_tag(v___x_515_) == 0)
{
lean_object* v_a_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_528_; 
v_a_516_ = lean_ctor_get(v___x_515_, 0);
v_isSharedCheck_528_ = !lean_is_exclusive(v___x_515_);
if (v_isSharedCheck_528_ == 0)
{
v___x_518_ = v___x_515_;
v_isShared_519_ = v_isSharedCheck_528_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_a_516_);
lean_dec(v___x_515_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_528_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
if (lean_obj_tag(v_a_516_) == 0)
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_1333__overap_522_; lean_object* v___x_523_; 
lean_dec_ref_known(v_a_516_, 1);
lean_del_object(v___x_518_);
v___x_520_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__0, &l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__0_once, _init_l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__0);
v___x_521_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__3, &l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__3_once, _init_l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__3);
v___x_1333__overap_522_ = l_panic___redArg(v___x_520_, v___x_521_);
lean_inc(v_a_505_);
lean_inc_ref(v_a_504_);
lean_inc(v_a_503_);
lean_inc_ref(v_a_502_);
lean_inc(v_a_501_);
lean_inc_ref(v_a_500_);
v___x_523_ = lean_apply_7(v___x_1333__overap_522_, v_a_500_, v_a_501_, v_a_502_, v_a_503_, v_a_504_, v_a_505_, lean_box(0));
return v___x_523_;
}
else
{
lean_object* v_a_524_; lean_object* v___x_526_; 
v_a_524_ = lean_ctor_get(v_a_516_, 0);
lean_inc(v_a_524_);
lean_dec_ref_known(v_a_516_, 1);
if (v_isShared_519_ == 0)
{
lean_ctor_set(v___x_518_, 0, v_a_524_);
v___x_526_ = v___x_518_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v_a_524_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
}
}
}
}
else
{
lean_object* v_a_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_536_; 
v_a_529_ = lean_ctor_get(v___x_515_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v___x_515_);
if (v_isSharedCheck_536_ == 0)
{
v___x_531_ = v___x_515_;
v_isShared_532_ = v_isSharedCheck_536_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_a_529_);
lean_dec(v___x_515_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_536_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v___x_534_; 
if (v_isShared_532_ == 0)
{
v___x_534_ = v___x_531_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v_a_529_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM___boxed(lean_object* v_00_u03b1_537_, lean_object* v_k_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l_Lean_Meta_Sym_Internal_liftBuilderM(v_00_u03b1_537_, v_k_538_, v_a_539_, v_a_540_, v_a_541_, v_a_542_, v_a_543_, v_a_544_);
lean_dec(v_a_544_);
lean_dec_ref(v_a_543_);
lean_dec(v_a_542_);
lean_dec_ref(v_a_541_);
lean_dec(v_a_540_);
lean_dec_ref(v_a_539_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_share1___redArg(lean_object* v_e_547_, lean_object* v_a_548_){
_start:
{
lean_object* v___x_549_; uint64_t v___x_550_; size_t v___x_551_; lean_object* v___x_552_; uint8_t v___x_553_; 
v___x_549_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy;
v___x_550_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_547_);
v___x_551_ = lean_uint64_to_usize(v___x_550_);
lean_inc_ref(v_e_547_);
lean_inc_ref(v_a_548_);
v___x_552_ = l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg(v_a_548_, v___x_551_, v_e_547_, v___x_549_);
v___x_553_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_552_, v___x_549_);
if (v___x_553_ == 0)
{
lean_object* v___x_554_; 
lean_dec_ref(v_e_547_);
v___x_554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_554_, 0, v___x_552_);
lean_ctor_set(v___x_554_, 1, v_a_548_);
return v___x_554_;
}
else
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
lean_dec_ref(v___x_552_);
v___x_555_ = lean_box(0);
lean_inc_ref(v_e_547_);
v___x_556_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1___redArg(v_a_548_, v_e_547_, v___x_555_);
v___x_557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_557_, 0, v_e_547_);
lean_ctor_set(v___x_557_, 1, v___x_556_);
return v___x_557_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_share1(lean_object* v_e_558_, uint8_t v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_){
_start:
{
lean_object* v___x_562_; 
v___x_562_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v_e_558_, v_a_561_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_share1___boxed(lean_object* v_e_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_){
_start:
{
uint8_t v_a_boxed_567_; lean_object* v_res_568_; 
v_a_boxed_567_ = lean_unbox(v_a_564_);
v_res_568_ = l_Lean_Meta_Sym_Internal_Builder_share1(v_e_563_, v_a_boxed_567_, v_a_565_, v_a_566_);
lean_dec_ref(v_a_565_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1(lean_object* v_msg_571_, uint8_t v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_){
_start:
{
lean_object* v___f_575_; lean_object* v___f_576_; lean_object* v___x_577_; lean_object* v___f_578_; lean_object* v___f_579_; lean_object* v___f_580_; lean_object* v___x_696__overap_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
v___f_575_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__0));
v___f_576_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__1));
v___x_577_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___f_575_, v___f_576_);
v___f_578_ = lean_alloc_closure((void*)(l_EStateM_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_578_, 0, v___x_577_);
v___f_579_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_579_, 0, v___f_578_);
v___f_580_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_580_, 0, v___f_579_);
v___x_696__overap_581_ = lean_panic_fn_borrowed(v___f_580_, v_msg_571_);
lean_dec_ref(v___f_580_);
v___x_582_ = lean_box(v___y_572_);
lean_inc_ref(v___y_573_);
v___x_583_ = lean_apply_3(v___x_696__overap_581_, v___x_582_, v___y_573_, v___y_574_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___boxed(lean_object* v_msg_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_){
_start:
{
uint8_t v___y_798__boxed_588_; lean_object* v_res_589_; 
v___y_798__boxed_588_ = lean_unbox(v___y_585_);
v_res_589_ = l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1(v_msg_584_, v___y_798__boxed_588_, v___y_586_, v___y_587_);
lean_dec_ref(v___y_586_);
return v_res_589_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_590_, lean_object* v_i_591_, lean_object* v_k_592_){
_start:
{
lean_object* v___x_593_; uint8_t v___x_594_; 
v___x_593_ = lean_array_get_size(v_keys_590_);
v___x_594_ = lean_nat_dec_lt(v_i_591_, v___x_593_);
if (v___x_594_ == 0)
{
lean_dec_ref(v_k_592_);
lean_dec(v_i_591_);
return v___x_594_;
}
else
{
lean_object* v_k_x27_595_; uint8_t v___x_596_; 
v_k_x27_595_ = lean_array_fget_borrowed(v_keys_590_, v_i_591_);
lean_inc(v_k_x27_595_);
lean_inc_ref(v_k_592_);
v___x_596_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_k_592_, v_k_x27_595_);
if (v___x_596_ == 0)
{
lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_597_ = lean_unsigned_to_nat(1u);
v___x_598_ = lean_nat_add(v_i_591_, v___x_597_);
lean_dec(v_i_591_);
v_i_591_ = v___x_598_;
goto _start;
}
else
{
lean_dec_ref(v_k_592_);
lean_dec(v_i_591_);
return v___x_596_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_600_, lean_object* v_i_601_, lean_object* v_k_602_){
_start:
{
uint8_t v_res_603_; lean_object* v_r_604_; 
v_res_603_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg(v_keys_600_, v_i_601_, v_k_602_);
lean_dec_ref(v_keys_600_);
v_r_604_ = lean_box(v_res_603_);
return v_r_604_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg(lean_object* v_x_605_, size_t v_x_606_, lean_object* v_x_607_){
_start:
{
if (lean_obj_tag(v_x_605_) == 0)
{
lean_object* v_es_608_; lean_object* v___x_609_; size_t v___x_610_; size_t v___x_611_; lean_object* v_j_612_; lean_object* v___x_613_; 
v_es_608_ = lean_ctor_get(v_x_605_, 0);
lean_inc_ref(v_es_608_);
lean_dec_ref_known(v_x_605_, 1);
v___x_609_ = lean_box(2);
v___x_610_ = ((size_t)31ULL);
v___x_611_ = lean_usize_land(v_x_606_, v___x_610_);
v_j_612_ = lean_usize_to_nat(v___x_611_);
v___x_613_ = lean_array_get(v___x_609_, v_es_608_, v_j_612_);
lean_dec(v_j_612_);
lean_dec_ref(v_es_608_);
switch(lean_obj_tag(v___x_613_))
{
case 0:
{
lean_object* v_key_614_; uint8_t v___x_615_; 
v_key_614_ = lean_ctor_get(v___x_613_, 0);
lean_inc(v_key_614_);
lean_dec_ref_known(v___x_613_, 2);
v___x_615_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_607_, v_key_614_);
return v___x_615_;
}
case 1:
{
lean_object* v_node_616_; size_t v___x_617_; size_t v___x_618_; 
v_node_616_ = lean_ctor_get(v___x_613_, 0);
lean_inc(v_node_616_);
lean_dec_ref_known(v___x_613_, 1);
v___x_617_ = ((size_t)5ULL);
v___x_618_ = lean_usize_shift_right(v_x_606_, v___x_617_);
v_x_605_ = v_node_616_;
v_x_606_ = v___x_618_;
goto _start;
}
default: 
{
uint8_t v___x_620_; 
lean_dec_ref(v_x_607_);
v___x_620_ = 0;
return v___x_620_;
}
}
}
else
{
lean_object* v_ks_621_; lean_object* v___x_622_; uint8_t v___x_623_; 
v_ks_621_ = lean_ctor_get(v_x_605_, 0);
lean_inc_ref(v_ks_621_);
lean_dec_ref_known(v_x_605_, 2);
v___x_622_ = lean_unsigned_to_nat(0u);
v___x_623_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg(v_ks_621_, v___x_622_, v_x_607_);
lean_dec_ref(v_ks_621_);
return v___x_623_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg___boxed(lean_object* v_x_624_, lean_object* v_x_625_, lean_object* v_x_626_){
_start:
{
size_t v_x_838__boxed_627_; uint8_t v_res_628_; lean_object* v_r_629_; 
v_x_838__boxed_627_ = lean_unbox_usize(v_x_625_);
lean_dec(v_x_625_);
v_res_628_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg(v_x_624_, v_x_838__boxed_627_, v_x_626_);
v_r_629_ = lean_box(v_res_628_);
return v_r_629_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg(lean_object* v_x_630_, lean_object* v_x_631_){
_start:
{
uint64_t v___x_632_; size_t v___x_633_; uint8_t v___x_634_; 
v___x_632_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_631_);
v___x_633_ = lean_uint64_to_usize(v___x_632_);
v___x_634_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg(v_x_630_, v___x_633_, v_x_631_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg___boxed(lean_object* v_x_635_, lean_object* v_x_636_){
_start:
{
uint8_t v_res_637_; lean_object* v_r_638_; 
v_res_637_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg(v_x_635_, v_x_636_);
v_r_638_ = lean_box(v_res_637_);
return v_r_638_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__2(void){
_start:
{
lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_641_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__1));
v___x_642_ = lean_unsigned_to_nat(2u);
v___x_643_ = lean_unsigned_to_nat(74u);
v___x_644_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__0));
v___x_645_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_646_ = l_mkPanicMessageWithDecl(v___x_645_, v___x_644_, v___x_643_, v___x_642_, v___x_641_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_assertShared(lean_object* v_e_647_, uint8_t v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_){
_start:
{
uint8_t v___x_651_; 
lean_inc_ref(v_a_650_);
v___x_651_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg(v_a_650_, v_e_647_);
if (v___x_651_ == 0)
{
lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_652_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__2, &l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__2_once, _init_l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__2);
v___x_653_ = l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1(v___x_652_, v_a_648_, v_a_649_, v_a_650_);
return v___x_653_;
}
else
{
lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_654_ = lean_box(0);
v___x_655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_655_, 0, v___x_654_);
lean_ctor_set(v___x_655_, 1, v_a_650_);
return v___x_655_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_assertShared___boxed(lean_object* v_e_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_){
_start:
{
uint8_t v_a_boxed_660_; lean_object* v_res_661_; 
v_a_boxed_660_ = lean_unbox(v_a_657_);
v_res_661_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_e_656_, v_a_boxed_660_, v_a_658_, v_a_659_);
lean_dec_ref(v_a_658_);
return v_res_661_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0(lean_object* v_00_u03b2_662_, lean_object* v_x_663_, lean_object* v_x_664_){
_start:
{
uint8_t v___x_665_; 
v___x_665_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg(v_x_663_, v_x_664_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___boxed(lean_object* v_00_u03b2_666_, lean_object* v_x_667_, lean_object* v_x_668_){
_start:
{
uint8_t v_res_669_; lean_object* v_r_670_; 
v_res_669_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0(v_00_u03b2_666_, v_x_667_, v_x_668_);
v_r_670_ = lean_box(v_res_669_);
return v_r_670_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0(lean_object* v_00_u03b2_671_, lean_object* v_x_672_, size_t v_x_673_, lean_object* v_x_674_){
_start:
{
uint8_t v___x_675_; 
v___x_675_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg(v_x_672_, v_x_673_, v_x_674_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___boxed(lean_object* v_00_u03b2_676_, lean_object* v_x_677_, lean_object* v_x_678_, lean_object* v_x_679_){
_start:
{
size_t v_x_937__boxed_680_; uint8_t v_res_681_; lean_object* v_r_682_; 
v_x_937__boxed_680_ = lean_unbox_usize(v_x_678_);
lean_dec(v_x_678_);
v_res_681_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0(v_00_u03b2_676_, v_x_677_, v_x_937__boxed_680_, v_x_679_);
v_r_682_ = lean_box(v_res_681_);
return v_r_682_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_683_, lean_object* v_keys_684_, lean_object* v_vals_685_, lean_object* v_heq_686_, lean_object* v_i_687_, lean_object* v_k_688_){
_start:
{
uint8_t v___x_689_; 
v___x_689_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg(v_keys_684_, v_i_687_, v_k_688_);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_690_, lean_object* v_keys_691_, lean_object* v_vals_692_, lean_object* v_heq_693_, lean_object* v_i_694_, lean_object* v_k_695_){
_start:
{
uint8_t v_res_696_; lean_object* v_r_697_; 
v_res_696_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2(v_00_u03b2_690_, v_keys_691_, v_vals_692_, v_heq_693_, v_i_694_, v_k_695_);
lean_dec_ref(v_vals_692_);
lean_dec_ref(v_keys_691_);
v_r_697_ = lean_box(v_res_696_);
return v_r_697_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__10(void){
_start:
{
lean_object* v___x_717_; lean_object* v___x_718_; 
v___x_717_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__9));
v___x_718_ = l_ReaderT_instMonad___redArg(v___x_717_);
return v___x_718_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__13(void){
_start:
{
lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_721_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__10, &l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__10_once, _init_l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__10);
v___x_722_ = lean_alloc_closure((void*)(l_ReaderT_read___boxed), 4, 3);
lean_closure_set(v___x_722_, 0, lean_box(0));
lean_closure_set(v___x_722_, 1, lean_box(0));
lean_closure_set(v___x_722_, 2, v___x_721_);
return v___x_722_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__14(void){
_start:
{
lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_723_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__13, &l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__13_once, _init_l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__13);
v___x_724_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__12));
v___x_725_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__11));
v___x_726_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_726_, 0, v___x_725_);
lean_ctor_set(v___x_726_, 1, v___x_724_);
lean_ctor_set(v___x_726_, 2, v___x_723_);
return v___x_726_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM(void){
_start:
{
lean_object* v___x_727_; 
v___x_727_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__14, &l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__14_once, _init_l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__14);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLitS___redArg(lean_object* v_inst_728_, lean_object* v_l_729_){
_start:
{
lean_object* v_share1_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
v_share1_730_ = lean_ctor_get(v_inst_728_, 0);
lean_inc(v_share1_730_);
lean_dec_ref(v_inst_728_);
v___x_731_ = l_Lean_Expr_lit___override(v_l_729_);
v___x_732_ = lean_apply_1(v_share1_730_, v___x_731_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLitS(lean_object* v_m_733_, lean_object* v_inst_734_, lean_object* v_l_735_){
_start:
{
lean_object* v___x_736_; 
v___x_736_ = l_Lean_Meta_Sym_Internal_mkLitS___redArg(v_inst_734_, v_l_735_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___redArg(lean_object* v_inst_737_, lean_object* v_declName_738_, lean_object* v_us_739_){
_start:
{
lean_object* v_share1_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
v_share1_740_ = lean_ctor_get(v_inst_737_, 0);
lean_inc(v_share1_740_);
lean_dec_ref(v_inst_737_);
v___x_741_ = l_Lean_Expr_const___override(v_declName_738_, v_us_739_);
v___x_742_ = lean_apply_1(v_share1_740_, v___x_741_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS(lean_object* v_m_743_, lean_object* v_inst_744_, lean_object* v_declName_745_, lean_object* v_us_746_){
_start:
{
lean_object* v___x_747_; 
v___x_747_ = l_Lean_Meta_Sym_Internal_mkConstS___redArg(v_inst_744_, v_declName_745_, v_us_746_);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___redArg(lean_object* v_inst_748_, lean_object* v_idx_749_){
_start:
{
lean_object* v_share1_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
v_share1_750_ = lean_ctor_get(v_inst_748_, 0);
lean_inc(v_share1_750_);
lean_dec_ref(v_inst_748_);
v___x_751_ = l_Lean_Expr_bvar___override(v_idx_749_);
v___x_752_ = lean_apply_1(v_share1_750_, v___x_751_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS(lean_object* v_m_753_, lean_object* v_inst_754_, lean_object* v_idx_755_){
_start:
{
lean_object* v___x_756_; 
v___x_756_ = l_Lean_Meta_Sym_Internal_mkBVarS___redArg(v_inst_754_, v_idx_755_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS___redArg(lean_object* v_inst_757_, lean_object* v_u_758_){
_start:
{
lean_object* v_share1_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v_share1_759_ = lean_ctor_get(v_inst_757_, 0);
lean_inc(v_share1_759_);
lean_dec_ref(v_inst_757_);
v___x_760_ = l_Lean_Expr_sort___override(v_u_758_);
v___x_761_ = lean_apply_1(v_share1_759_, v___x_760_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS(lean_object* v_m_762_, lean_object* v_inst_763_, lean_object* v_u_764_){
_start:
{
lean_object* v___x_765_; 
v___x_765_ = l_Lean_Meta_Sym_Internal_mkSortS___redArg(v_inst_763_, v_u_764_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___redArg(lean_object* v_inst_766_, lean_object* v_fvarId_767_){
_start:
{
lean_object* v_share1_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v_share1_768_ = lean_ctor_get(v_inst_766_, 0);
lean_inc(v_share1_768_);
lean_dec_ref(v_inst_766_);
v___x_769_ = l_Lean_Expr_fvar___override(v_fvarId_767_);
v___x_770_ = lean_apply_1(v_share1_768_, v___x_769_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS(lean_object* v_m_771_, lean_object* v_inst_772_, lean_object* v_fvarId_773_){
_start:
{
lean_object* v___x_774_; 
v___x_774_ = l_Lean_Meta_Sym_Internal_mkFVarS___redArg(v_inst_772_, v_fvarId_773_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMVarS___redArg(lean_object* v_inst_775_, lean_object* v_mvarId_776_){
_start:
{
lean_object* v_share1_777_; lean_object* v___x_778_; lean_object* v___x_779_; 
v_share1_777_ = lean_ctor_get(v_inst_775_, 0);
lean_inc(v_share1_777_);
lean_dec_ref(v_inst_775_);
v___x_778_ = l_Lean_Expr_mvar___override(v_mvarId_776_);
v___x_779_ = lean_apply_1(v_share1_777_, v___x_778_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMVarS(lean_object* v_m_780_, lean_object* v_inst_781_, lean_object* v_mvarId_782_){
_start:
{
lean_object* v___x_783_; 
v___x_783_ = l_Lean_Meta_Sym_Internal_mkMVarS___redArg(v_inst_781_, v_mvarId_782_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__0(lean_object* v_d_784_, lean_object* v_e_785_, lean_object* v_share1_786_, lean_object* v_____r_787_){
_start:
{
lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_788_ = l_Lean_Expr_mdata___override(v_d_784_, v_e_785_);
v___x_789_ = lean_apply_1(v_share1_786_, v___x_788_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1(lean_object* v___f_790_, lean_object* v_____r_791_){
_start:
{
lean_object* v___x_792_; 
v___x_792_ = lean_apply_1(v___f_790_, v_____r_791_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__2(lean_object* v___f_793_, lean_object* v_assertShared_794_, lean_object* v_e_795_, lean_object* v_toBind_796_, lean_object* v___f_797_, uint8_t v_____do__lift_798_){
_start:
{
if (v_____do__lift_798_ == 0)
{
lean_object* v___x_799_; lean_object* v___x_800_; 
lean_dec(v___f_797_);
lean_dec(v_toBind_796_);
lean_dec_ref(v_e_795_);
lean_dec(v_assertShared_794_);
v___x_799_ = lean_box(0);
v___x_800_ = lean_apply_1(v___f_793_, v___x_799_);
return v___x_800_;
}
else
{
lean_object* v___x_801_; lean_object* v___x_802_; 
lean_dec(v___f_793_);
v___x_801_ = lean_apply_1(v_assertShared_794_, v_e_795_);
v___x_802_ = lean_apply_4(v_toBind_796_, lean_box(0), lean_box(0), v___x_801_, v___f_797_);
return v___x_802_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__2___boxed(lean_object* v___f_803_, lean_object* v_assertShared_804_, lean_object* v_e_805_, lean_object* v_toBind_806_, lean_object* v___f_807_, lean_object* v_____do__lift_808_){
_start:
{
uint8_t v_____do__lift_86__boxed_809_; lean_object* v_res_810_; 
v_____do__lift_86__boxed_809_ = lean_unbox(v_____do__lift_808_);
v_res_810_ = l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__2(v___f_803_, v_assertShared_804_, v_e_805_, v_toBind_806_, v___f_807_, v_____do__lift_86__boxed_809_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg(lean_object* v_inst_811_, lean_object* v_inst_812_, lean_object* v_d_813_, lean_object* v_e_814_){
_start:
{
lean_object* v_toBind_815_; lean_object* v_share1_816_; lean_object* v_assertShared_817_; lean_object* v_isDebugEnabled_818_; lean_object* v___f_819_; lean_object* v___f_820_; lean_object* v___f_821_; lean_object* v___x_822_; 
v_toBind_815_ = lean_ctor_get(v_inst_812_, 1);
lean_inc_n(v_toBind_815_, 2);
lean_dec_ref(v_inst_812_);
v_share1_816_ = lean_ctor_get(v_inst_811_, 0);
lean_inc(v_share1_816_);
v_assertShared_817_ = lean_ctor_get(v_inst_811_, 1);
lean_inc(v_assertShared_817_);
v_isDebugEnabled_818_ = lean_ctor_get(v_inst_811_, 2);
lean_inc(v_isDebugEnabled_818_);
lean_dec_ref(v_inst_811_);
lean_inc_ref(v_e_814_);
v___f_819_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__0), 4, 3);
lean_closure_set(v___f_819_, 0, v_d_813_);
lean_closure_set(v___f_819_, 1, v_e_814_);
lean_closure_set(v___f_819_, 2, v_share1_816_);
lean_inc_ref(v___f_819_);
v___f_820_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_820_, 0, v___f_819_);
v___f_821_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_821_, 0, v___f_819_);
lean_closure_set(v___f_821_, 1, v_assertShared_817_);
lean_closure_set(v___f_821_, 2, v_e_814_);
lean_closure_set(v___f_821_, 3, v_toBind_815_);
lean_closure_set(v___f_821_, 4, v___f_820_);
v___x_822_ = lean_apply_4(v_toBind_815_, lean_box(0), lean_box(0), v_isDebugEnabled_818_, v___f_821_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS(lean_object* v_m_823_, lean_object* v_inst_824_, lean_object* v_inst_825_, lean_object* v_d_826_, lean_object* v_e_827_){
_start:
{
lean_object* v___x_828_; 
v___x_828_ = l_Lean_Meta_Sym_Internal_mkMDataS___redArg(v_inst_824_, v_inst_825_, v_d_826_, v_e_827_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__0(lean_object* v_structName_829_, lean_object* v_idx_830_, lean_object* v_struct_831_, lean_object* v_share1_832_, lean_object* v_____r_833_){
_start:
{
lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_834_ = l_Lean_Expr_proj___override(v_structName_829_, v_idx_830_, v_struct_831_);
v___x_835_ = lean_apply_1(v_share1_832_, v___x_834_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__2(lean_object* v___f_836_, lean_object* v_assertShared_837_, lean_object* v_struct_838_, lean_object* v_toBind_839_, lean_object* v___f_840_, uint8_t v_____do__lift_841_){
_start:
{
if (v_____do__lift_841_ == 0)
{
lean_object* v___x_842_; lean_object* v___x_843_; 
lean_dec(v___f_840_);
lean_dec(v_toBind_839_);
lean_dec_ref(v_struct_838_);
lean_dec(v_assertShared_837_);
v___x_842_ = lean_box(0);
v___x_843_ = lean_apply_1(v___f_836_, v___x_842_);
return v___x_843_;
}
else
{
lean_object* v___x_844_; lean_object* v___x_845_; 
lean_dec(v___f_836_);
v___x_844_ = lean_apply_1(v_assertShared_837_, v_struct_838_);
v___x_845_ = lean_apply_4(v_toBind_839_, lean_box(0), lean_box(0), v___x_844_, v___f_840_);
return v___x_845_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__2___boxed(lean_object* v___f_846_, lean_object* v_assertShared_847_, lean_object* v_struct_848_, lean_object* v_toBind_849_, lean_object* v___f_850_, lean_object* v_____do__lift_851_){
_start:
{
uint8_t v_____do__lift_80__boxed_852_; lean_object* v_res_853_; 
v_____do__lift_80__boxed_852_ = lean_unbox(v_____do__lift_851_);
v_res_853_ = l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__2(v___f_846_, v_assertShared_847_, v_struct_848_, v_toBind_849_, v___f_850_, v_____do__lift_80__boxed_852_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___redArg(lean_object* v_inst_854_, lean_object* v_inst_855_, lean_object* v_structName_856_, lean_object* v_idx_857_, lean_object* v_struct_858_){
_start:
{
lean_object* v_toBind_859_; lean_object* v_share1_860_; lean_object* v_assertShared_861_; lean_object* v_isDebugEnabled_862_; lean_object* v___f_863_; lean_object* v___f_864_; lean_object* v___f_865_; lean_object* v___x_866_; 
v_toBind_859_ = lean_ctor_get(v_inst_855_, 1);
lean_inc_n(v_toBind_859_, 2);
lean_dec_ref(v_inst_855_);
v_share1_860_ = lean_ctor_get(v_inst_854_, 0);
lean_inc(v_share1_860_);
v_assertShared_861_ = lean_ctor_get(v_inst_854_, 1);
lean_inc(v_assertShared_861_);
v_isDebugEnabled_862_ = lean_ctor_get(v_inst_854_, 2);
lean_inc(v_isDebugEnabled_862_);
lean_dec_ref(v_inst_854_);
lean_inc_ref(v_struct_858_);
v___f_863_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__0), 5, 4);
lean_closure_set(v___f_863_, 0, v_structName_856_);
lean_closure_set(v___f_863_, 1, v_idx_857_);
lean_closure_set(v___f_863_, 2, v_struct_858_);
lean_closure_set(v___f_863_, 3, v_share1_860_);
lean_inc_ref(v___f_863_);
v___f_864_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_864_, 0, v___f_863_);
v___f_865_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_865_, 0, v___f_863_);
lean_closure_set(v___f_865_, 1, v_assertShared_861_);
lean_closure_set(v___f_865_, 2, v_struct_858_);
lean_closure_set(v___f_865_, 3, v_toBind_859_);
lean_closure_set(v___f_865_, 4, v___f_864_);
v___x_866_ = lean_apply_4(v_toBind_859_, lean_box(0), lean_box(0), v_isDebugEnabled_862_, v___f_865_);
return v___x_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS(lean_object* v_m_867_, lean_object* v_inst_868_, lean_object* v_inst_869_, lean_object* v_structName_870_, lean_object* v_idx_871_, lean_object* v_struct_872_){
_start:
{
lean_object* v___x_873_; 
v___x_873_ = l_Lean_Meta_Sym_Internal_mkProjS___redArg(v_inst_868_, v_inst_869_, v_structName_870_, v_idx_871_, v_struct_872_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__0(lean_object* v_f_874_, lean_object* v_a_875_, lean_object* v_share1_876_, lean_object* v_____r_877_){
_start:
{
lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_878_ = l_Lean_Expr_app___override(v_f_874_, v_a_875_);
v___x_879_ = lean_apply_1(v_share1_876_, v___x_878_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__2(lean_object* v_assertShared_880_, lean_object* v_a_881_, lean_object* v_toBind_882_, lean_object* v___f_883_, lean_object* v_____r_884_){
_start:
{
lean_object* v___x_885_; lean_object* v___x_886_; 
v___x_885_ = lean_apply_1(v_assertShared_880_, v_a_881_);
v___x_886_ = lean_apply_4(v_toBind_882_, lean_box(0), lean_box(0), v___x_885_, v___f_883_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__1(lean_object* v___f_887_, lean_object* v_assertShared_888_, lean_object* v_a_889_, lean_object* v_toBind_890_, lean_object* v___f_891_, lean_object* v_f_892_, uint8_t v_____do__lift_893_){
_start:
{
if (v_____do__lift_893_ == 0)
{
lean_object* v___x_894_; lean_object* v___x_895_; 
lean_dec_ref(v_f_892_);
lean_dec(v___f_891_);
lean_dec(v_toBind_890_);
lean_dec_ref(v_a_889_);
lean_dec(v_assertShared_888_);
v___x_894_ = lean_box(0);
v___x_895_ = lean_apply_1(v___f_887_, v___x_894_);
return v___x_895_;
}
else
{
lean_object* v___f_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
lean_dec(v___f_887_);
lean_inc(v_toBind_890_);
lean_inc(v_assertShared_888_);
v___f_896_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__2), 5, 4);
lean_closure_set(v___f_896_, 0, v_assertShared_888_);
lean_closure_set(v___f_896_, 1, v_a_889_);
lean_closure_set(v___f_896_, 2, v_toBind_890_);
lean_closure_set(v___f_896_, 3, v___f_891_);
v___x_897_ = lean_apply_1(v_assertShared_888_, v_f_892_);
v___x_898_ = lean_apply_4(v_toBind_890_, lean_box(0), lean_box(0), v___x_897_, v___f_896_);
return v___x_898_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__1___boxed(lean_object* v___f_899_, lean_object* v_assertShared_900_, lean_object* v_a_901_, lean_object* v_toBind_902_, lean_object* v___f_903_, lean_object* v_f_904_, lean_object* v_____do__lift_905_){
_start:
{
uint8_t v_____do__lift_105__boxed_906_; lean_object* v_res_907_; 
v_____do__lift_105__boxed_906_ = lean_unbox(v_____do__lift_905_);
v_res_907_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__1(v___f_899_, v_assertShared_900_, v_a_901_, v_toBind_902_, v___f_903_, v_f_904_, v_____do__lift_105__boxed_906_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg(lean_object* v_inst_908_, lean_object* v_inst_909_, lean_object* v_f_910_, lean_object* v_a_911_){
_start:
{
lean_object* v_toBind_912_; lean_object* v_share1_913_; lean_object* v_assertShared_914_; lean_object* v_isDebugEnabled_915_; lean_object* v___f_916_; lean_object* v___f_917_; lean_object* v___f_918_; lean_object* v___x_919_; 
v_toBind_912_ = lean_ctor_get(v_inst_909_, 1);
lean_inc_n(v_toBind_912_, 2);
lean_dec_ref(v_inst_909_);
v_share1_913_ = lean_ctor_get(v_inst_908_, 0);
lean_inc(v_share1_913_);
v_assertShared_914_ = lean_ctor_get(v_inst_908_, 1);
lean_inc(v_assertShared_914_);
v_isDebugEnabled_915_ = lean_ctor_get(v_inst_908_, 2);
lean_inc(v_isDebugEnabled_915_);
lean_dec_ref(v_inst_908_);
lean_inc_ref(v_a_911_);
lean_inc_ref(v_f_910_);
v___f_916_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__0), 4, 3);
lean_closure_set(v___f_916_, 0, v_f_910_);
lean_closure_set(v___f_916_, 1, v_a_911_);
lean_closure_set(v___f_916_, 2, v_share1_913_);
lean_inc_ref(v___f_916_);
v___f_917_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_917_, 0, v___f_916_);
v___f_918_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_918_, 0, v___f_916_);
lean_closure_set(v___f_918_, 1, v_assertShared_914_);
lean_closure_set(v___f_918_, 2, v_a_911_);
lean_closure_set(v___f_918_, 3, v_toBind_912_);
lean_closure_set(v___f_918_, 4, v___f_917_);
lean_closure_set(v___f_918_, 5, v_f_910_);
v___x_919_ = lean_apply_4(v_toBind_912_, lean_box(0), lean_box(0), v_isDebugEnabled_915_, v___f_918_);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS(lean_object* v_m_920_, lean_object* v_inst_921_, lean_object* v_inst_922_, lean_object* v_f_923_, lean_object* v_a_924_){
_start:
{
lean_object* v___x_925_; 
v___x_925_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_921_, v_inst_922_, v_f_923_, v_a_924_);
return v___x_925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__0(lean_object* v_x_926_, lean_object* v_t_927_, lean_object* v_b_928_, uint8_t v_bi_929_, lean_object* v_share1_930_, lean_object* v_____r_931_){
_start:
{
lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_932_ = l_Lean_Expr_lam___override(v_x_926_, v_t_927_, v_b_928_, v_bi_929_);
v___x_933_ = lean_apply_1(v_share1_930_, v___x_932_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__0___boxed(lean_object* v_x_934_, lean_object* v_t_935_, lean_object* v_b_936_, lean_object* v_bi_937_, lean_object* v_share1_938_, lean_object* v_____r_939_){
_start:
{
uint8_t v_bi_boxed_940_; lean_object* v_res_941_; 
v_bi_boxed_940_ = lean_unbox(v_bi_937_);
v_res_941_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__0(v_x_934_, v_t_935_, v_b_936_, v_bi_boxed_940_, v_share1_938_, v_____r_939_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__2(lean_object* v_assertShared_942_, lean_object* v_b_943_, lean_object* v_toBind_944_, lean_object* v___f_945_, lean_object* v_____r_946_){
_start:
{
lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_947_ = lean_apply_1(v_assertShared_942_, v_b_943_);
v___x_948_ = lean_apply_4(v_toBind_944_, lean_box(0), lean_box(0), v___x_947_, v___f_945_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1(lean_object* v___f_949_, lean_object* v_assertShared_950_, lean_object* v_b_951_, lean_object* v_toBind_952_, lean_object* v___f_953_, lean_object* v_t_954_, uint8_t v_____do__lift_955_){
_start:
{
if (v_____do__lift_955_ == 0)
{
lean_object* v___x_956_; lean_object* v___x_957_; 
lean_dec_ref(v_t_954_);
lean_dec(v___f_953_);
lean_dec(v_toBind_952_);
lean_dec_ref(v_b_951_);
lean_dec(v_assertShared_950_);
v___x_956_ = lean_box(0);
v___x_957_ = lean_apply_1(v___f_949_, v___x_956_);
return v___x_957_;
}
else
{
lean_object* v___f_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
lean_dec(v___f_949_);
lean_inc(v_toBind_952_);
lean_inc(v_assertShared_950_);
v___f_958_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__2), 5, 4);
lean_closure_set(v___f_958_, 0, v_assertShared_950_);
lean_closure_set(v___f_958_, 1, v_b_951_);
lean_closure_set(v___f_958_, 2, v_toBind_952_);
lean_closure_set(v___f_958_, 3, v___f_953_);
v___x_959_ = lean_apply_1(v_assertShared_950_, v_t_954_);
v___x_960_ = lean_apply_4(v_toBind_952_, lean_box(0), lean_box(0), v___x_959_, v___f_958_);
return v___x_960_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1___boxed(lean_object* v___f_961_, lean_object* v_assertShared_962_, lean_object* v_b_963_, lean_object* v_toBind_964_, lean_object* v___f_965_, lean_object* v_t_966_, lean_object* v_____do__lift_967_){
_start:
{
uint8_t v_____do__lift_106__boxed_968_; lean_object* v_res_969_; 
v_____do__lift_106__boxed_968_ = lean_unbox(v_____do__lift_967_);
v_res_969_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1(v___f_961_, v_assertShared_962_, v_b_963_, v_toBind_964_, v___f_965_, v_t_966_, v_____do__lift_106__boxed_968_);
return v_res_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(lean_object* v_inst_970_, lean_object* v_inst_971_, lean_object* v_x_972_, uint8_t v_bi_973_, lean_object* v_t_974_, lean_object* v_b_975_){
_start:
{
lean_object* v_toBind_976_; lean_object* v_share1_977_; lean_object* v_assertShared_978_; lean_object* v_isDebugEnabled_979_; lean_object* v___x_980_; lean_object* v___f_981_; lean_object* v___f_982_; lean_object* v___f_983_; lean_object* v___x_984_; 
v_toBind_976_ = lean_ctor_get(v_inst_971_, 1);
lean_inc_n(v_toBind_976_, 2);
lean_dec_ref(v_inst_971_);
v_share1_977_ = lean_ctor_get(v_inst_970_, 0);
lean_inc(v_share1_977_);
v_assertShared_978_ = lean_ctor_get(v_inst_970_, 1);
lean_inc(v_assertShared_978_);
v_isDebugEnabled_979_ = lean_ctor_get(v_inst_970_, 2);
lean_inc(v_isDebugEnabled_979_);
lean_dec_ref(v_inst_970_);
v___x_980_ = lean_box(v_bi_973_);
lean_inc_ref(v_b_975_);
lean_inc_ref(v_t_974_);
v___f_981_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_981_, 0, v_x_972_);
lean_closure_set(v___f_981_, 1, v_t_974_);
lean_closure_set(v___f_981_, 2, v_b_975_);
lean_closure_set(v___f_981_, 3, v___x_980_);
lean_closure_set(v___f_981_, 4, v_share1_977_);
lean_inc_ref(v___f_981_);
v___f_982_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_982_, 0, v___f_981_);
v___f_983_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_983_, 0, v___f_981_);
lean_closure_set(v___f_983_, 1, v_assertShared_978_);
lean_closure_set(v___f_983_, 2, v_b_975_);
lean_closure_set(v___f_983_, 3, v_toBind_976_);
lean_closure_set(v___f_983_, 4, v___f_982_);
lean_closure_set(v___f_983_, 5, v_t_974_);
v___x_984_ = lean_apply_4(v_toBind_976_, lean_box(0), lean_box(0), v_isDebugEnabled_979_, v___f_983_);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___boxed(lean_object* v_inst_985_, lean_object* v_inst_986_, lean_object* v_x_987_, lean_object* v_bi_988_, lean_object* v_t_989_, lean_object* v_b_990_){
_start:
{
uint8_t v_bi_boxed_991_; lean_object* v_res_992_; 
v_bi_boxed_991_ = lean_unbox(v_bi_988_);
v_res_992_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v_inst_985_, v_inst_986_, v_x_987_, v_bi_boxed_991_, v_t_989_, v_b_990_);
return v_res_992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS(lean_object* v_m_993_, lean_object* v_inst_994_, lean_object* v_inst_995_, lean_object* v_x_996_, uint8_t v_bi_997_, lean_object* v_t_998_, lean_object* v_b_999_){
_start:
{
lean_object* v___x_1000_; 
v___x_1000_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v_inst_994_, v_inst_995_, v_x_996_, v_bi_997_, v_t_998_, v_b_999_);
return v___x_1000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___boxed(lean_object* v_m_1001_, lean_object* v_inst_1002_, lean_object* v_inst_1003_, lean_object* v_x_1004_, lean_object* v_bi_1005_, lean_object* v_t_1006_, lean_object* v_b_1007_){
_start:
{
uint8_t v_bi_boxed_1008_; lean_object* v_res_1009_; 
v_bi_boxed_1008_ = lean_unbox(v_bi_1005_);
v_res_1009_ = l_Lean_Meta_Sym_Internal_mkLambdaS(v_m_1001_, v_inst_1002_, v_inst_1003_, v_x_1004_, v_bi_boxed_1008_, v_t_1006_, v_b_1007_);
return v_res_1009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___redArg___lam__0(lean_object* v_x_1010_, lean_object* v_t_1011_, lean_object* v_b_1012_, uint8_t v_bi_1013_, lean_object* v_share1_1014_, lean_object* v_____r_1015_){
_start:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1016_ = l_Lean_Expr_forallE___override(v_x_1010_, v_t_1011_, v_b_1012_, v_bi_1013_);
v___x_1017_ = lean_apply_1(v_share1_1014_, v___x_1016_);
return v___x_1017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___redArg___lam__0___boxed(lean_object* v_x_1018_, lean_object* v_t_1019_, lean_object* v_b_1020_, lean_object* v_bi_1021_, lean_object* v_share1_1022_, lean_object* v_____r_1023_){
_start:
{
uint8_t v_bi_boxed_1024_; lean_object* v_res_1025_; 
v_bi_boxed_1024_ = lean_unbox(v_bi_1021_);
v_res_1025_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg___lam__0(v_x_1018_, v_t_1019_, v_b_1020_, v_bi_boxed_1024_, v_share1_1022_, v_____r_1023_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___redArg(lean_object* v_inst_1026_, lean_object* v_inst_1027_, lean_object* v_x_1028_, uint8_t v_bi_1029_, lean_object* v_t_1030_, lean_object* v_b_1031_){
_start:
{
lean_object* v_toBind_1032_; lean_object* v_share1_1033_; lean_object* v_assertShared_1034_; lean_object* v_isDebugEnabled_1035_; lean_object* v___x_1036_; lean_object* v___f_1037_; lean_object* v___f_1038_; lean_object* v___f_1039_; lean_object* v___x_1040_; 
v_toBind_1032_ = lean_ctor_get(v_inst_1027_, 1);
lean_inc_n(v_toBind_1032_, 2);
lean_dec_ref(v_inst_1027_);
v_share1_1033_ = lean_ctor_get(v_inst_1026_, 0);
lean_inc(v_share1_1033_);
v_assertShared_1034_ = lean_ctor_get(v_inst_1026_, 1);
lean_inc(v_assertShared_1034_);
v_isDebugEnabled_1035_ = lean_ctor_get(v_inst_1026_, 2);
lean_inc(v_isDebugEnabled_1035_);
lean_dec_ref(v_inst_1026_);
v___x_1036_ = lean_box(v_bi_1029_);
lean_inc_ref(v_b_1031_);
lean_inc_ref(v_t_1030_);
v___f_1037_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkForallS___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1037_, 0, v_x_1028_);
lean_closure_set(v___f_1037_, 1, v_t_1030_);
lean_closure_set(v___f_1037_, 2, v_b_1031_);
lean_closure_set(v___f_1037_, 3, v___x_1036_);
lean_closure_set(v___f_1037_, 4, v_share1_1033_);
lean_inc_ref(v___f_1037_);
v___f_1038_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1038_, 0, v___f_1037_);
v___f_1039_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_1039_, 0, v___f_1037_);
lean_closure_set(v___f_1039_, 1, v_assertShared_1034_);
lean_closure_set(v___f_1039_, 2, v_b_1031_);
lean_closure_set(v___f_1039_, 3, v_toBind_1032_);
lean_closure_set(v___f_1039_, 4, v___f_1038_);
lean_closure_set(v___f_1039_, 5, v_t_1030_);
v___x_1040_ = lean_apply_4(v_toBind_1032_, lean_box(0), lean_box(0), v_isDebugEnabled_1035_, v___f_1039_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___redArg___boxed(lean_object* v_inst_1041_, lean_object* v_inst_1042_, lean_object* v_x_1043_, lean_object* v_bi_1044_, lean_object* v_t_1045_, lean_object* v_b_1046_){
_start:
{
uint8_t v_bi_boxed_1047_; lean_object* v_res_1048_; 
v_bi_boxed_1047_ = lean_unbox(v_bi_1044_);
v_res_1048_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v_inst_1041_, v_inst_1042_, v_x_1043_, v_bi_boxed_1047_, v_t_1045_, v_b_1046_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS(lean_object* v_m_1049_, lean_object* v_inst_1050_, lean_object* v_inst_1051_, lean_object* v_x_1052_, uint8_t v_bi_1053_, lean_object* v_t_1054_, lean_object* v_b_1055_){
_start:
{
lean_object* v___x_1056_; 
v___x_1056_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v_inst_1050_, v_inst_1051_, v_x_1052_, v_bi_1053_, v_t_1054_, v_b_1055_);
return v___x_1056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___boxed(lean_object* v_m_1057_, lean_object* v_inst_1058_, lean_object* v_inst_1059_, lean_object* v_x_1060_, lean_object* v_bi_1061_, lean_object* v_t_1062_, lean_object* v_b_1063_){
_start:
{
uint8_t v_bi_boxed_1064_; lean_object* v_res_1065_; 
v_bi_boxed_1064_ = lean_unbox(v_bi_1061_);
v_res_1065_ = l_Lean_Meta_Sym_Internal_mkForallS(v_m_1057_, v_inst_1058_, v_inst_1059_, v_x_1060_, v_bi_boxed_1064_, v_t_1062_, v_b_1063_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__0(lean_object* v_x_1066_, lean_object* v_t_1067_, lean_object* v_v_1068_, lean_object* v_b_1069_, uint8_t v_nondep_1070_, lean_object* v_share1_1071_, lean_object* v_____r_1072_){
_start:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1073_ = l_Lean_Expr_letE___override(v_x_1066_, v_t_1067_, v_v_1068_, v_b_1069_, v_nondep_1070_);
v___x_1074_ = lean_apply_1(v_share1_1071_, v___x_1073_);
return v___x_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__0___boxed(lean_object* v_x_1075_, lean_object* v_t_1076_, lean_object* v_v_1077_, lean_object* v_b_1078_, lean_object* v_nondep_1079_, lean_object* v_share1_1080_, lean_object* v_____r_1081_){
_start:
{
uint8_t v_nondep_boxed_1082_; lean_object* v_res_1083_; 
v_nondep_boxed_1082_ = lean_unbox(v_nondep_1079_);
v_res_1083_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__0(v_x_1075_, v_t_1076_, v_v_1077_, v_b_1078_, v_nondep_boxed_1082_, v_share1_1080_, v_____r_1081_);
return v_res_1083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__3(lean_object* v_assertShared_1084_, lean_object* v_v_1085_, lean_object* v_toBind_1086_, lean_object* v___f_1087_, lean_object* v_____r_1088_){
_start:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1089_ = lean_apply_1(v_assertShared_1084_, v_v_1085_);
v___x_1090_ = lean_apply_4(v_toBind_1086_, lean_box(0), lean_box(0), v___x_1089_, v___f_1087_);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1(lean_object* v___f_1091_, lean_object* v_assertShared_1092_, lean_object* v_b_1093_, lean_object* v_toBind_1094_, lean_object* v___f_1095_, lean_object* v_v_1096_, lean_object* v_t_1097_, uint8_t v_____do__lift_1098_){
_start:
{
if (v_____do__lift_1098_ == 0)
{
lean_object* v___x_1099_; lean_object* v___x_1100_; 
lean_dec_ref(v_t_1097_);
lean_dec_ref(v_v_1096_);
lean_dec(v___f_1095_);
lean_dec(v_toBind_1094_);
lean_dec_ref(v_b_1093_);
lean_dec(v_assertShared_1092_);
v___x_1099_ = lean_box(0);
v___x_1100_ = lean_apply_1(v___f_1091_, v___x_1099_);
return v___x_1100_;
}
else
{
lean_object* v___f_1101_; lean_object* v___f_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; 
lean_dec(v___f_1091_);
lean_inc_n(v_toBind_1094_, 2);
lean_inc_n(v_assertShared_1092_, 2);
v___f_1101_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__2), 5, 4);
lean_closure_set(v___f_1101_, 0, v_assertShared_1092_);
lean_closure_set(v___f_1101_, 1, v_b_1093_);
lean_closure_set(v___f_1101_, 2, v_toBind_1094_);
lean_closure_set(v___f_1101_, 3, v___f_1095_);
v___f_1102_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__3), 5, 4);
lean_closure_set(v___f_1102_, 0, v_assertShared_1092_);
lean_closure_set(v___f_1102_, 1, v_v_1096_);
lean_closure_set(v___f_1102_, 2, v_toBind_1094_);
lean_closure_set(v___f_1102_, 3, v___f_1101_);
v___x_1103_ = lean_apply_1(v_assertShared_1092_, v_t_1097_);
v___x_1104_ = lean_apply_4(v_toBind_1094_, lean_box(0), lean_box(0), v___x_1103_, v___f_1102_);
return v___x_1104_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1___boxed(lean_object* v___f_1105_, lean_object* v_assertShared_1106_, lean_object* v_b_1107_, lean_object* v_toBind_1108_, lean_object* v___f_1109_, lean_object* v_v_1110_, lean_object* v_t_1111_, lean_object* v_____do__lift_1112_){
_start:
{
uint8_t v_____do__lift_123__boxed_1113_; lean_object* v_res_1114_; 
v_____do__lift_123__boxed_1113_ = lean_unbox(v_____do__lift_1112_);
v_res_1114_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1(v___f_1105_, v_assertShared_1106_, v_b_1107_, v_toBind_1108_, v___f_1109_, v_v_1110_, v_t_1111_, v_____do__lift_123__boxed_1113_);
return v_res_1114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg(lean_object* v_inst_1115_, lean_object* v_inst_1116_, lean_object* v_x_1117_, lean_object* v_t_1118_, lean_object* v_v_1119_, lean_object* v_b_1120_, uint8_t v_nondep_1121_){
_start:
{
lean_object* v_toBind_1122_; lean_object* v_share1_1123_; lean_object* v_assertShared_1124_; lean_object* v_isDebugEnabled_1125_; lean_object* v___x_1126_; lean_object* v___f_1127_; lean_object* v___f_1128_; lean_object* v___f_1129_; lean_object* v___x_1130_; 
v_toBind_1122_ = lean_ctor_get(v_inst_1116_, 1);
lean_inc_n(v_toBind_1122_, 2);
lean_dec_ref(v_inst_1116_);
v_share1_1123_ = lean_ctor_get(v_inst_1115_, 0);
lean_inc(v_share1_1123_);
v_assertShared_1124_ = lean_ctor_get(v_inst_1115_, 1);
lean_inc(v_assertShared_1124_);
v_isDebugEnabled_1125_ = lean_ctor_get(v_inst_1115_, 2);
lean_inc(v_isDebugEnabled_1125_);
lean_dec_ref(v_inst_1115_);
v___x_1126_ = lean_box(v_nondep_1121_);
lean_inc_ref(v_b_1120_);
lean_inc_ref(v_v_1119_);
lean_inc_ref(v_t_1118_);
v___f_1127_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_1127_, 0, v_x_1117_);
lean_closure_set(v___f_1127_, 1, v_t_1118_);
lean_closure_set(v___f_1127_, 2, v_v_1119_);
lean_closure_set(v___f_1127_, 3, v_b_1120_);
lean_closure_set(v___f_1127_, 4, v___x_1126_);
lean_closure_set(v___f_1127_, 5, v_share1_1123_);
lean_inc_ref(v___f_1127_);
v___f_1128_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1128_, 0, v___f_1127_);
v___f_1129_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_1129_, 0, v___f_1127_);
lean_closure_set(v___f_1129_, 1, v_assertShared_1124_);
lean_closure_set(v___f_1129_, 2, v_b_1120_);
lean_closure_set(v___f_1129_, 3, v_toBind_1122_);
lean_closure_set(v___f_1129_, 4, v___f_1128_);
lean_closure_set(v___f_1129_, 5, v_v_1119_);
lean_closure_set(v___f_1129_, 6, v_t_1118_);
v___x_1130_ = lean_apply_4(v_toBind_1122_, lean_box(0), lean_box(0), v_isDebugEnabled_1125_, v___f_1129_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___boxed(lean_object* v_inst_1131_, lean_object* v_inst_1132_, lean_object* v_x_1133_, lean_object* v_t_1134_, lean_object* v_v_1135_, lean_object* v_b_1136_, lean_object* v_nondep_1137_){
_start:
{
uint8_t v_nondep_boxed_1138_; lean_object* v_res_1139_; 
v_nondep_boxed_1138_ = lean_unbox(v_nondep_1137_);
v_res_1139_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1131_, v_inst_1132_, v_x_1133_, v_t_1134_, v_v_1135_, v_b_1136_, v_nondep_boxed_1138_);
return v_res_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS(lean_object* v_m_1140_, lean_object* v_inst_1141_, lean_object* v_inst_1142_, lean_object* v_x_1143_, lean_object* v_t_1144_, lean_object* v_v_1145_, lean_object* v_b_1146_, uint8_t v_nondep_1147_){
_start:
{
lean_object* v___x_1148_; 
v___x_1148_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1141_, v_inst_1142_, v_x_1143_, v_t_1144_, v_v_1145_, v_b_1146_, v_nondep_1147_);
return v___x_1148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___boxed(lean_object* v_m_1149_, lean_object* v_inst_1150_, lean_object* v_inst_1151_, lean_object* v_x_1152_, lean_object* v_t_1153_, lean_object* v_v_1154_, lean_object* v_b_1155_, lean_object* v_nondep_1156_){
_start:
{
uint8_t v_nondep_boxed_1157_; lean_object* v_res_1158_; 
v_nondep_boxed_1157_ = lean_unbox(v_nondep_1156_);
v_res_1158_ = l_Lean_Meta_Sym_Internal_mkLetS(v_m_1149_, v_inst_1150_, v_inst_1151_, v_x_1152_, v_t_1153_, v_v_1154_, v_b_1155_, v_nondep_boxed_1157_);
return v_res_1158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkHaveS___redArg___lam__0(lean_object* v_x_1159_, lean_object* v_t_1160_, lean_object* v_v_1161_, lean_object* v_b_1162_, lean_object* v_share1_1163_, lean_object* v_____r_1164_){
_start:
{
uint8_t v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1165_ = 1;
v___x_1166_ = l_Lean_Expr_letE___override(v_x_1159_, v_t_1160_, v_v_1161_, v_b_1162_, v___x_1165_);
v___x_1167_ = lean_apply_1(v_share1_1163_, v___x_1166_);
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkHaveS___redArg(lean_object* v_inst_1168_, lean_object* v_inst_1169_, lean_object* v_x_1170_, lean_object* v_t_1171_, lean_object* v_v_1172_, lean_object* v_b_1173_){
_start:
{
lean_object* v_toBind_1174_; lean_object* v_share1_1175_; lean_object* v_assertShared_1176_; lean_object* v_isDebugEnabled_1177_; lean_object* v___f_1178_; lean_object* v___f_1179_; lean_object* v___f_1180_; lean_object* v___x_1181_; 
v_toBind_1174_ = lean_ctor_get(v_inst_1169_, 1);
lean_inc_n(v_toBind_1174_, 2);
lean_dec_ref(v_inst_1169_);
v_share1_1175_ = lean_ctor_get(v_inst_1168_, 0);
lean_inc(v_share1_1175_);
v_assertShared_1176_ = lean_ctor_get(v_inst_1168_, 1);
lean_inc(v_assertShared_1176_);
v_isDebugEnabled_1177_ = lean_ctor_get(v_inst_1168_, 2);
lean_inc(v_isDebugEnabled_1177_);
lean_dec_ref(v_inst_1168_);
lean_inc_ref(v_b_1173_);
lean_inc_ref(v_v_1172_);
lean_inc_ref(v_t_1171_);
v___f_1178_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkHaveS___redArg___lam__0), 6, 5);
lean_closure_set(v___f_1178_, 0, v_x_1170_);
lean_closure_set(v___f_1178_, 1, v_t_1171_);
lean_closure_set(v___f_1178_, 2, v_v_1172_);
lean_closure_set(v___f_1178_, 3, v_b_1173_);
lean_closure_set(v___f_1178_, 4, v_share1_1175_);
lean_inc_ref(v___f_1178_);
v___f_1179_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1179_, 0, v___f_1178_);
v___f_1180_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_1180_, 0, v___f_1178_);
lean_closure_set(v___f_1180_, 1, v_assertShared_1176_);
lean_closure_set(v___f_1180_, 2, v_b_1173_);
lean_closure_set(v___f_1180_, 3, v_toBind_1174_);
lean_closure_set(v___f_1180_, 4, v___f_1179_);
lean_closure_set(v___f_1180_, 5, v_v_1172_);
lean_closure_set(v___f_1180_, 6, v_t_1171_);
v___x_1181_ = lean_apply_4(v_toBind_1174_, lean_box(0), lean_box(0), v_isDebugEnabled_1177_, v___f_1180_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkHaveS(lean_object* v_m_1182_, lean_object* v_inst_1183_, lean_object* v_inst_1184_, lean_object* v_x_1185_, lean_object* v_t_1186_, lean_object* v_v_1187_, lean_object* v_b_1188_){
_start:
{
lean_object* v___x_1189_; 
v___x_1189_ = l_Lean_Meta_Sym_Internal_mkHaveS___redArg(v_inst_1183_, v_inst_1184_, v_x_1185_, v_t_1186_, v_v_1187_, v_b_1188_);
return v___x_1189_;
}
}
static lean_object* _init_l_Lean_Expr_updateAppS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1192_ = ((lean_object*)(l_Lean_Expr_updateAppS_x21___redArg___closed__1));
v___x_1193_ = lean_unsigned_to_nat(25u);
v___x_1194_ = lean_unsigned_to_nat(148u);
v___x_1195_ = ((lean_object*)(l_Lean_Expr_updateAppS_x21___redArg___closed__0));
v___x_1196_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1197_ = l_mkPanicMessageWithDecl(v___x_1196_, v___x_1195_, v___x_1194_, v___x_1193_, v___x_1192_);
return v___x_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateAppS_x21___redArg(lean_object* v_inst_1198_, lean_object* v_inst_1199_, lean_object* v_e_1200_, lean_object* v_newFn_1201_, lean_object* v_newArg_1202_){
_start:
{
uint8_t v___y_1204_; 
if (lean_obj_tag(v_e_1200_) == 5)
{
lean_object* v_fn_1209_; lean_object* v_arg_1210_; uint8_t v___x_1211_; 
v_fn_1209_ = lean_ctor_get(v_e_1200_, 0);
v_arg_1210_ = lean_ctor_get(v_e_1200_, 1);
v___x_1211_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fn_1209_, v_newFn_1201_);
if (v___x_1211_ == 0)
{
v___y_1204_ = v___x_1211_;
goto v___jp_1203_;
}
else
{
uint8_t v___x_1212_; 
v___x_1212_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_1210_, v_newArg_1202_);
v___y_1204_ = v___x_1212_;
goto v___jp_1203_;
}
}
else
{
lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; 
lean_dec_ref(v_newArg_1202_);
lean_dec_ref(v_newFn_1201_);
lean_dec_ref(v_e_1200_);
lean_dec_ref(v_inst_1198_);
v___x_1213_ = l_Lean_instInhabitedExpr;
v___x_1214_ = l_instInhabitedOfMonad___redArg(v_inst_1199_, v___x_1213_);
v___x_1215_ = lean_obj_once(&l_Lean_Expr_updateAppS_x21___redArg___closed__2, &l_Lean_Expr_updateAppS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateAppS_x21___redArg___closed__2);
v___x_1216_ = l_panic___redArg(v___x_1214_, v___x_1215_);
lean_dec(v___x_1214_);
return v___x_1216_;
}
v___jp_1203_:
{
if (v___y_1204_ == 0)
{
lean_object* v___x_1205_; 
lean_dec_ref(v_e_1200_);
v___x_1205_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1198_, v_inst_1199_, v_newFn_1201_, v_newArg_1202_);
return v___x_1205_;
}
else
{
lean_object* v_toApplicative_1206_; lean_object* v_toPure_1207_; lean_object* v___x_1208_; 
lean_dec_ref(v_newArg_1202_);
lean_dec_ref(v_newFn_1201_);
lean_dec_ref(v_inst_1198_);
v_toApplicative_1206_ = lean_ctor_get(v_inst_1199_, 0);
lean_inc_ref(v_toApplicative_1206_);
lean_dec_ref(v_inst_1199_);
v_toPure_1207_ = lean_ctor_get(v_toApplicative_1206_, 1);
lean_inc(v_toPure_1207_);
lean_dec_ref(v_toApplicative_1206_);
v___x_1208_ = lean_apply_2(v_toPure_1207_, lean_box(0), v_e_1200_);
return v___x_1208_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateAppS_x21(lean_object* v_m_1217_, lean_object* v_inst_1218_, lean_object* v_inst_1219_, lean_object* v_e_1220_, lean_object* v_newFn_1221_, lean_object* v_newArg_1222_){
_start:
{
uint8_t v___y_1224_; 
if (lean_obj_tag(v_e_1220_) == 5)
{
lean_object* v_fn_1229_; lean_object* v_arg_1230_; uint8_t v___x_1231_; 
v_fn_1229_ = lean_ctor_get(v_e_1220_, 0);
v_arg_1230_ = lean_ctor_get(v_e_1220_, 1);
v___x_1231_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fn_1229_, v_newFn_1221_);
if (v___x_1231_ == 0)
{
v___y_1224_ = v___x_1231_;
goto v___jp_1223_;
}
else
{
uint8_t v___x_1232_; 
v___x_1232_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_1230_, v_newArg_1222_);
v___y_1224_ = v___x_1232_;
goto v___jp_1223_;
}
}
else
{
lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; 
lean_dec_ref(v_newArg_1222_);
lean_dec_ref(v_newFn_1221_);
lean_dec_ref(v_e_1220_);
lean_dec_ref(v_inst_1218_);
v___x_1233_ = l_Lean_instInhabitedExpr;
v___x_1234_ = l_instInhabitedOfMonad___redArg(v_inst_1219_, v___x_1233_);
v___x_1235_ = lean_obj_once(&l_Lean_Expr_updateAppS_x21___redArg___closed__2, &l_Lean_Expr_updateAppS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateAppS_x21___redArg___closed__2);
v___x_1236_ = l_panic___redArg(v___x_1234_, v___x_1235_);
lean_dec(v___x_1234_);
return v___x_1236_;
}
v___jp_1223_:
{
if (v___y_1224_ == 0)
{
lean_object* v___x_1225_; 
lean_dec_ref(v_e_1220_);
v___x_1225_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1218_, v_inst_1219_, v_newFn_1221_, v_newArg_1222_);
return v___x_1225_;
}
else
{
lean_object* v_toApplicative_1226_; lean_object* v_toPure_1227_; lean_object* v___x_1228_; 
lean_dec_ref(v_newArg_1222_);
lean_dec_ref(v_newFn_1221_);
lean_dec_ref(v_inst_1218_);
v_toApplicative_1226_ = lean_ctor_get(v_inst_1219_, 0);
lean_inc_ref(v_toApplicative_1226_);
lean_dec_ref(v_inst_1219_);
v_toPure_1227_ = lean_ctor_get(v_toApplicative_1226_, 1);
lean_inc(v_toPure_1227_);
lean_dec_ref(v_toApplicative_1226_);
v___x_1228_ = lean_apply_2(v_toPure_1227_, lean_box(0), v_e_1220_);
return v___x_1228_;
}
}
}
}
static lean_object* _init_l_Lean_Expr_updateMDataS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1239_ = ((lean_object*)(l_Lean_Expr_updateMDataS_x21___redArg___closed__1));
v___x_1240_ = lean_unsigned_to_nat(24u);
v___x_1241_ = lean_unsigned_to_nat(152u);
v___x_1242_ = ((lean_object*)(l_Lean_Expr_updateMDataS_x21___redArg___closed__0));
v___x_1243_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1244_ = l_mkPanicMessageWithDecl(v___x_1243_, v___x_1242_, v___x_1241_, v___x_1240_, v___x_1239_);
return v___x_1244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateMDataS_x21___redArg(lean_object* v_inst_1245_, lean_object* v_inst_1246_, lean_object* v_e_1247_, lean_object* v_newExpr_1248_){
_start:
{
if (lean_obj_tag(v_e_1247_) == 10)
{
lean_object* v_data_1249_; lean_object* v_expr_1250_; uint8_t v___x_1251_; 
v_data_1249_ = lean_ctor_get(v_e_1247_, 0);
v_expr_1250_ = lean_ctor_get(v_e_1247_, 1);
v___x_1251_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_expr_1250_, v_newExpr_1248_);
if (v___x_1251_ == 0)
{
lean_object* v___x_1252_; 
lean_inc(v_data_1249_);
lean_dec_ref_known(v_e_1247_, 2);
v___x_1252_ = l_Lean_Meta_Sym_Internal_mkMDataS___redArg(v_inst_1245_, v_inst_1246_, v_data_1249_, v_newExpr_1248_);
return v___x_1252_;
}
else
{
lean_object* v_toApplicative_1253_; lean_object* v_toPure_1254_; lean_object* v___x_1255_; 
lean_dec_ref(v_newExpr_1248_);
lean_dec_ref(v_inst_1245_);
v_toApplicative_1253_ = lean_ctor_get(v_inst_1246_, 0);
lean_inc_ref(v_toApplicative_1253_);
lean_dec_ref(v_inst_1246_);
v_toPure_1254_ = lean_ctor_get(v_toApplicative_1253_, 1);
lean_inc(v_toPure_1254_);
lean_dec_ref(v_toApplicative_1253_);
v___x_1255_ = lean_apply_2(v_toPure_1254_, lean_box(0), v_e_1247_);
return v___x_1255_;
}
}
else
{
lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; 
lean_dec_ref(v_newExpr_1248_);
lean_dec_ref(v_e_1247_);
lean_dec_ref(v_inst_1245_);
v___x_1256_ = l_Lean_instInhabitedExpr;
v___x_1257_ = l_instInhabitedOfMonad___redArg(v_inst_1246_, v___x_1256_);
v___x_1258_ = lean_obj_once(&l_Lean_Expr_updateMDataS_x21___redArg___closed__2, &l_Lean_Expr_updateMDataS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateMDataS_x21___redArg___closed__2);
v___x_1259_ = l_panic___redArg(v___x_1257_, v___x_1258_);
lean_dec(v___x_1257_);
return v___x_1259_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateMDataS_x21(lean_object* v_m_1260_, lean_object* v_inst_1261_, lean_object* v_inst_1262_, lean_object* v_e_1263_, lean_object* v_newExpr_1264_){
_start:
{
if (lean_obj_tag(v_e_1263_) == 10)
{
lean_object* v_data_1265_; lean_object* v_expr_1266_; uint8_t v___x_1267_; 
v_data_1265_ = lean_ctor_get(v_e_1263_, 0);
v_expr_1266_ = lean_ctor_get(v_e_1263_, 1);
v___x_1267_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_expr_1266_, v_newExpr_1264_);
if (v___x_1267_ == 0)
{
lean_object* v___x_1268_; 
lean_inc(v_data_1265_);
lean_dec_ref_known(v_e_1263_, 2);
v___x_1268_ = l_Lean_Meta_Sym_Internal_mkMDataS___redArg(v_inst_1261_, v_inst_1262_, v_data_1265_, v_newExpr_1264_);
return v___x_1268_;
}
else
{
lean_object* v_toApplicative_1269_; lean_object* v_toPure_1270_; lean_object* v___x_1271_; 
lean_dec_ref(v_newExpr_1264_);
lean_dec_ref(v_inst_1261_);
v_toApplicative_1269_ = lean_ctor_get(v_inst_1262_, 0);
lean_inc_ref(v_toApplicative_1269_);
lean_dec_ref(v_inst_1262_);
v_toPure_1270_ = lean_ctor_get(v_toApplicative_1269_, 1);
lean_inc(v_toPure_1270_);
lean_dec_ref(v_toApplicative_1269_);
v___x_1271_ = lean_apply_2(v_toPure_1270_, lean_box(0), v_e_1263_);
return v___x_1271_;
}
}
else
{
lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; 
lean_dec_ref(v_newExpr_1264_);
lean_dec_ref(v_e_1263_);
lean_dec_ref(v_inst_1261_);
v___x_1272_ = l_Lean_instInhabitedExpr;
v___x_1273_ = l_instInhabitedOfMonad___redArg(v_inst_1262_, v___x_1272_);
v___x_1274_ = lean_obj_once(&l_Lean_Expr_updateMDataS_x21___redArg___closed__2, &l_Lean_Expr_updateMDataS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateMDataS_x21___redArg___closed__2);
v___x_1275_ = l_panic___redArg(v___x_1273_, v___x_1274_);
lean_dec(v___x_1273_);
return v___x_1275_;
}
}
}
static lean_object* _init_l_Lean_Expr_updateProjS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; 
v___x_1278_ = ((lean_object*)(l_Lean_Expr_updateProjS_x21___redArg___closed__1));
v___x_1279_ = lean_unsigned_to_nat(25u);
v___x_1280_ = lean_unsigned_to_nat(156u);
v___x_1281_ = ((lean_object*)(l_Lean_Expr_updateProjS_x21___redArg___closed__0));
v___x_1282_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1283_ = l_mkPanicMessageWithDecl(v___x_1282_, v___x_1281_, v___x_1280_, v___x_1279_, v___x_1278_);
return v___x_1283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateProjS_x21___redArg(lean_object* v_inst_1284_, lean_object* v_inst_1285_, lean_object* v_e_1286_, lean_object* v_newExpr_1287_){
_start:
{
if (lean_obj_tag(v_e_1286_) == 11)
{
lean_object* v_typeName_1288_; lean_object* v_idx_1289_; lean_object* v_struct_1290_; uint8_t v___x_1291_; 
v_typeName_1288_ = lean_ctor_get(v_e_1286_, 0);
v_idx_1289_ = lean_ctor_get(v_e_1286_, 1);
v_struct_1290_ = lean_ctor_get(v_e_1286_, 2);
v___x_1291_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_1290_, v_newExpr_1287_);
if (v___x_1291_ == 0)
{
lean_object* v___x_1292_; 
lean_inc(v_idx_1289_);
lean_inc(v_typeName_1288_);
lean_dec_ref_known(v_e_1286_, 3);
v___x_1292_ = l_Lean_Meta_Sym_Internal_mkProjS___redArg(v_inst_1284_, v_inst_1285_, v_typeName_1288_, v_idx_1289_, v_newExpr_1287_);
return v___x_1292_;
}
else
{
lean_object* v_toApplicative_1293_; lean_object* v_toPure_1294_; lean_object* v___x_1295_; 
lean_dec_ref(v_newExpr_1287_);
lean_dec_ref(v_inst_1284_);
v_toApplicative_1293_ = lean_ctor_get(v_inst_1285_, 0);
lean_inc_ref(v_toApplicative_1293_);
lean_dec_ref(v_inst_1285_);
v_toPure_1294_ = lean_ctor_get(v_toApplicative_1293_, 1);
lean_inc(v_toPure_1294_);
lean_dec_ref(v_toApplicative_1293_);
v___x_1295_ = lean_apply_2(v_toPure_1294_, lean_box(0), v_e_1286_);
return v___x_1295_;
}
}
else
{
lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; 
lean_dec_ref(v_newExpr_1287_);
lean_dec_ref(v_e_1286_);
lean_dec_ref(v_inst_1284_);
v___x_1296_ = l_Lean_instInhabitedExpr;
v___x_1297_ = l_instInhabitedOfMonad___redArg(v_inst_1285_, v___x_1296_);
v___x_1298_ = lean_obj_once(&l_Lean_Expr_updateProjS_x21___redArg___closed__2, &l_Lean_Expr_updateProjS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateProjS_x21___redArg___closed__2);
v___x_1299_ = l_panic___redArg(v___x_1297_, v___x_1298_);
lean_dec(v___x_1297_);
return v___x_1299_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateProjS_x21(lean_object* v_m_1300_, lean_object* v_inst_1301_, lean_object* v_inst_1302_, lean_object* v_e_1303_, lean_object* v_newExpr_1304_){
_start:
{
if (lean_obj_tag(v_e_1303_) == 11)
{
lean_object* v_typeName_1305_; lean_object* v_idx_1306_; lean_object* v_struct_1307_; uint8_t v___x_1308_; 
v_typeName_1305_ = lean_ctor_get(v_e_1303_, 0);
v_idx_1306_ = lean_ctor_get(v_e_1303_, 1);
v_struct_1307_ = lean_ctor_get(v_e_1303_, 2);
v___x_1308_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_1307_, v_newExpr_1304_);
if (v___x_1308_ == 0)
{
lean_object* v___x_1309_; 
lean_inc(v_idx_1306_);
lean_inc(v_typeName_1305_);
lean_dec_ref_known(v_e_1303_, 3);
v___x_1309_ = l_Lean_Meta_Sym_Internal_mkProjS___redArg(v_inst_1301_, v_inst_1302_, v_typeName_1305_, v_idx_1306_, v_newExpr_1304_);
return v___x_1309_;
}
else
{
lean_object* v_toApplicative_1310_; lean_object* v_toPure_1311_; lean_object* v___x_1312_; 
lean_dec_ref(v_newExpr_1304_);
lean_dec_ref(v_inst_1301_);
v_toApplicative_1310_ = lean_ctor_get(v_inst_1302_, 0);
lean_inc_ref(v_toApplicative_1310_);
lean_dec_ref(v_inst_1302_);
v_toPure_1311_ = lean_ctor_get(v_toApplicative_1310_, 1);
lean_inc(v_toPure_1311_);
lean_dec_ref(v_toApplicative_1310_);
v___x_1312_ = lean_apply_2(v_toPure_1311_, lean_box(0), v_e_1303_);
return v___x_1312_;
}
}
else
{
lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; 
lean_dec_ref(v_newExpr_1304_);
lean_dec_ref(v_e_1303_);
lean_dec_ref(v_inst_1301_);
v___x_1313_ = l_Lean_instInhabitedExpr;
v___x_1314_ = l_instInhabitedOfMonad___redArg(v_inst_1302_, v___x_1313_);
v___x_1315_ = lean_obj_once(&l_Lean_Expr_updateProjS_x21___redArg___closed__2, &l_Lean_Expr_updateProjS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateProjS_x21___redArg___closed__2);
v___x_1316_ = l_panic___redArg(v___x_1314_, v___x_1315_);
lean_dec(v___x_1314_);
return v___x_1316_;
}
}
}
static lean_object* _init_l_Lean_Expr_updateForallS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; 
v___x_1319_ = ((lean_object*)(l_Lean_Expr_updateForallS_x21___redArg___closed__1));
v___x_1320_ = lean_unsigned_to_nat(31u);
v___x_1321_ = lean_unsigned_to_nat(160u);
v___x_1322_ = ((lean_object*)(l_Lean_Expr_updateForallS_x21___redArg___closed__0));
v___x_1323_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1324_ = l_mkPanicMessageWithDecl(v___x_1323_, v___x_1322_, v___x_1321_, v___x_1320_, v___x_1319_);
return v___x_1324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallS_x21___redArg(lean_object* v_inst_1325_, lean_object* v_inst_1326_, lean_object* v_e_1327_, lean_object* v_newDomain_1328_, lean_object* v_newBody_1329_){
_start:
{
if (lean_obj_tag(v_e_1327_) == 7)
{
lean_object* v_binderName_1330_; lean_object* v_binderType_1331_; lean_object* v_body_1332_; uint8_t v_binderInfo_1333_; uint8_t v___y_1335_; uint8_t v___x_1340_; 
v_binderName_1330_ = lean_ctor_get(v_e_1327_, 0);
v_binderType_1331_ = lean_ctor_get(v_e_1327_, 1);
v_body_1332_ = lean_ctor_get(v_e_1327_, 2);
v_binderInfo_1333_ = lean_ctor_get_uint8(v_e_1327_, sizeof(void*)*3 + 8);
v___x_1340_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_1331_, v_newDomain_1328_);
if (v___x_1340_ == 0)
{
v___y_1335_ = v___x_1340_;
goto v___jp_1334_;
}
else
{
uint8_t v___x_1341_; 
v___x_1341_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1332_, v_newBody_1329_);
v___y_1335_ = v___x_1341_;
goto v___jp_1334_;
}
v___jp_1334_:
{
if (v___y_1335_ == 0)
{
lean_object* v___x_1336_; 
lean_inc(v_binderName_1330_);
lean_dec_ref_known(v_e_1327_, 3);
v___x_1336_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v_inst_1325_, v_inst_1326_, v_binderName_1330_, v_binderInfo_1333_, v_newDomain_1328_, v_newBody_1329_);
return v___x_1336_;
}
else
{
lean_object* v_toApplicative_1337_; lean_object* v_toPure_1338_; lean_object* v___x_1339_; 
lean_dec_ref(v_newBody_1329_);
lean_dec_ref(v_newDomain_1328_);
lean_dec_ref(v_inst_1325_);
v_toApplicative_1337_ = lean_ctor_get(v_inst_1326_, 0);
lean_inc_ref(v_toApplicative_1337_);
lean_dec_ref(v_inst_1326_);
v_toPure_1338_ = lean_ctor_get(v_toApplicative_1337_, 1);
lean_inc(v_toPure_1338_);
lean_dec_ref(v_toApplicative_1337_);
v___x_1339_ = lean_apply_2(v_toPure_1338_, lean_box(0), v_e_1327_);
return v___x_1339_;
}
}
}
else
{
lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; 
lean_dec_ref(v_newBody_1329_);
lean_dec_ref(v_newDomain_1328_);
lean_dec_ref(v_e_1327_);
lean_dec_ref(v_inst_1325_);
v___x_1342_ = l_Lean_instInhabitedExpr;
v___x_1343_ = l_instInhabitedOfMonad___redArg(v_inst_1326_, v___x_1342_);
v___x_1344_ = lean_obj_once(&l_Lean_Expr_updateForallS_x21___redArg___closed__2, &l_Lean_Expr_updateForallS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateForallS_x21___redArg___closed__2);
v___x_1345_ = l_panic___redArg(v___x_1343_, v___x_1344_);
lean_dec(v___x_1343_);
return v___x_1345_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallS_x21(lean_object* v_m_1346_, lean_object* v_inst_1347_, lean_object* v_inst_1348_, lean_object* v_e_1349_, lean_object* v_newDomain_1350_, lean_object* v_newBody_1351_){
_start:
{
if (lean_obj_tag(v_e_1349_) == 7)
{
lean_object* v_binderName_1352_; lean_object* v_binderType_1353_; lean_object* v_body_1354_; uint8_t v_binderInfo_1355_; uint8_t v___y_1357_; uint8_t v___x_1362_; 
v_binderName_1352_ = lean_ctor_get(v_e_1349_, 0);
v_binderType_1353_ = lean_ctor_get(v_e_1349_, 1);
v_body_1354_ = lean_ctor_get(v_e_1349_, 2);
v_binderInfo_1355_ = lean_ctor_get_uint8(v_e_1349_, sizeof(void*)*3 + 8);
v___x_1362_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_1353_, v_newDomain_1350_);
if (v___x_1362_ == 0)
{
v___y_1357_ = v___x_1362_;
goto v___jp_1356_;
}
else
{
uint8_t v___x_1363_; 
v___x_1363_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1354_, v_newBody_1351_);
v___y_1357_ = v___x_1363_;
goto v___jp_1356_;
}
v___jp_1356_:
{
if (v___y_1357_ == 0)
{
lean_object* v___x_1358_; 
lean_inc(v_binderName_1352_);
lean_dec_ref_known(v_e_1349_, 3);
v___x_1358_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v_inst_1347_, v_inst_1348_, v_binderName_1352_, v_binderInfo_1355_, v_newDomain_1350_, v_newBody_1351_);
return v___x_1358_;
}
else
{
lean_object* v_toApplicative_1359_; lean_object* v_toPure_1360_; lean_object* v___x_1361_; 
lean_dec_ref(v_newBody_1351_);
lean_dec_ref(v_newDomain_1350_);
lean_dec_ref(v_inst_1347_);
v_toApplicative_1359_ = lean_ctor_get(v_inst_1348_, 0);
lean_inc_ref(v_toApplicative_1359_);
lean_dec_ref(v_inst_1348_);
v_toPure_1360_ = lean_ctor_get(v_toApplicative_1359_, 1);
lean_inc(v_toPure_1360_);
lean_dec_ref(v_toApplicative_1359_);
v___x_1361_ = lean_apply_2(v_toPure_1360_, lean_box(0), v_e_1349_);
return v___x_1361_;
}
}
}
else
{
lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; 
lean_dec_ref(v_newBody_1351_);
lean_dec_ref(v_newDomain_1350_);
lean_dec_ref(v_e_1349_);
lean_dec_ref(v_inst_1347_);
v___x_1364_ = l_Lean_instInhabitedExpr;
v___x_1365_ = l_instInhabitedOfMonad___redArg(v_inst_1348_, v___x_1364_);
v___x_1366_ = lean_obj_once(&l_Lean_Expr_updateForallS_x21___redArg___closed__2, &l_Lean_Expr_updateForallS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateForallS_x21___redArg___closed__2);
v___x_1367_ = l_panic___redArg(v___x_1365_, v___x_1366_);
lean_dec(v___x_1365_);
return v___x_1367_;
}
}
}
static lean_object* _init_l_Lean_Expr_updateLambdaS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; 
v___x_1370_ = ((lean_object*)(l_Lean_Expr_updateLambdaS_x21___redArg___closed__1));
v___x_1371_ = lean_unsigned_to_nat(27u);
v___x_1372_ = lean_unsigned_to_nat(167u);
v___x_1373_ = ((lean_object*)(l_Lean_Expr_updateLambdaS_x21___redArg___closed__0));
v___x_1374_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1375_ = l_mkPanicMessageWithDecl(v___x_1374_, v___x_1373_, v___x_1372_, v___x_1371_, v___x_1370_);
return v___x_1375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLambdaS_x21___redArg(lean_object* v_inst_1376_, lean_object* v_inst_1377_, lean_object* v_e_1378_, lean_object* v_newDomain_1379_, lean_object* v_newBody_1380_){
_start:
{
if (lean_obj_tag(v_e_1378_) == 6)
{
lean_object* v_binderName_1381_; lean_object* v_binderType_1382_; lean_object* v_body_1383_; uint8_t v_binderInfo_1384_; uint8_t v___y_1386_; uint8_t v___x_1391_; 
v_binderName_1381_ = lean_ctor_get(v_e_1378_, 0);
v_binderType_1382_ = lean_ctor_get(v_e_1378_, 1);
v_body_1383_ = lean_ctor_get(v_e_1378_, 2);
v_binderInfo_1384_ = lean_ctor_get_uint8(v_e_1378_, sizeof(void*)*3 + 8);
v___x_1391_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_1382_, v_newDomain_1379_);
if (v___x_1391_ == 0)
{
v___y_1386_ = v___x_1391_;
goto v___jp_1385_;
}
else
{
uint8_t v___x_1392_; 
v___x_1392_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1383_, v_newBody_1380_);
v___y_1386_ = v___x_1392_;
goto v___jp_1385_;
}
v___jp_1385_:
{
if (v___y_1386_ == 0)
{
lean_object* v___x_1387_; 
lean_inc(v_binderName_1381_);
lean_dec_ref_known(v_e_1378_, 3);
v___x_1387_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v_inst_1376_, v_inst_1377_, v_binderName_1381_, v_binderInfo_1384_, v_newDomain_1379_, v_newBody_1380_);
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
lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; 
lean_dec_ref(v_newBody_1380_);
lean_dec_ref(v_newDomain_1379_);
lean_dec_ref(v_e_1378_);
lean_dec_ref(v_inst_1376_);
v___x_1393_ = l_Lean_instInhabitedExpr;
v___x_1394_ = l_instInhabitedOfMonad___redArg(v_inst_1377_, v___x_1393_);
v___x_1395_ = lean_obj_once(&l_Lean_Expr_updateLambdaS_x21___redArg___closed__2, &l_Lean_Expr_updateLambdaS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateLambdaS_x21___redArg___closed__2);
v___x_1396_ = l_panic___redArg(v___x_1394_, v___x_1395_);
lean_dec(v___x_1394_);
return v___x_1396_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLambdaS_x21(lean_object* v_m_1397_, lean_object* v_inst_1398_, lean_object* v_inst_1399_, lean_object* v_e_1400_, lean_object* v_newDomain_1401_, lean_object* v_newBody_1402_){
_start:
{
if (lean_obj_tag(v_e_1400_) == 6)
{
lean_object* v_binderName_1403_; lean_object* v_binderType_1404_; lean_object* v_body_1405_; uint8_t v_binderInfo_1406_; uint8_t v___y_1408_; uint8_t v___x_1413_; 
v_binderName_1403_ = lean_ctor_get(v_e_1400_, 0);
v_binderType_1404_ = lean_ctor_get(v_e_1400_, 1);
v_body_1405_ = lean_ctor_get(v_e_1400_, 2);
v_binderInfo_1406_ = lean_ctor_get_uint8(v_e_1400_, sizeof(void*)*3 + 8);
v___x_1413_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_1404_, v_newDomain_1401_);
if (v___x_1413_ == 0)
{
v___y_1408_ = v___x_1413_;
goto v___jp_1407_;
}
else
{
uint8_t v___x_1414_; 
v___x_1414_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1405_, v_newBody_1402_);
v___y_1408_ = v___x_1414_;
goto v___jp_1407_;
}
v___jp_1407_:
{
if (v___y_1408_ == 0)
{
lean_object* v___x_1409_; 
lean_inc(v_binderName_1403_);
lean_dec_ref_known(v_e_1400_, 3);
v___x_1409_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v_inst_1398_, v_inst_1399_, v_binderName_1403_, v_binderInfo_1406_, v_newDomain_1401_, v_newBody_1402_);
return v___x_1409_;
}
else
{
lean_object* v_toApplicative_1410_; lean_object* v_toPure_1411_; lean_object* v___x_1412_; 
lean_dec_ref(v_newBody_1402_);
lean_dec_ref(v_newDomain_1401_);
lean_dec_ref(v_inst_1398_);
v_toApplicative_1410_ = lean_ctor_get(v_inst_1399_, 0);
lean_inc_ref(v_toApplicative_1410_);
lean_dec_ref(v_inst_1399_);
v_toPure_1411_ = lean_ctor_get(v_toApplicative_1410_, 1);
lean_inc(v_toPure_1411_);
lean_dec_ref(v_toApplicative_1410_);
v___x_1412_ = lean_apply_2(v_toPure_1411_, lean_box(0), v_e_1400_);
return v___x_1412_;
}
}
}
else
{
lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; 
lean_dec_ref(v_newBody_1402_);
lean_dec_ref(v_newDomain_1401_);
lean_dec_ref(v_e_1400_);
lean_dec_ref(v_inst_1398_);
v___x_1415_ = l_Lean_instInhabitedExpr;
v___x_1416_ = l_instInhabitedOfMonad___redArg(v_inst_1399_, v___x_1415_);
v___x_1417_ = lean_obj_once(&l_Lean_Expr_updateLambdaS_x21___redArg___closed__2, &l_Lean_Expr_updateLambdaS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateLambdaS_x21___redArg___closed__2);
v___x_1418_ = l_panic___redArg(v___x_1416_, v___x_1417_);
lean_dec(v___x_1416_);
return v___x_1418_;
}
}
}
static lean_object* _init_l_Lean_Expr_updateLetS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; 
v___x_1421_ = ((lean_object*)(l_Lean_Expr_updateLetS_x21___redArg___closed__1));
v___x_1422_ = lean_unsigned_to_nat(34u);
v___x_1423_ = lean_unsigned_to_nat(174u);
v___x_1424_ = ((lean_object*)(l_Lean_Expr_updateLetS_x21___redArg___closed__0));
v___x_1425_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1426_ = l_mkPanicMessageWithDecl(v___x_1425_, v___x_1424_, v___x_1423_, v___x_1422_, v___x_1421_);
return v___x_1426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLetS_x21___redArg(lean_object* v_inst_1427_, lean_object* v_inst_1428_, lean_object* v_e_1429_, lean_object* v_newType_1430_, lean_object* v_newVal_1431_, lean_object* v_newBody_1432_){
_start:
{
if (lean_obj_tag(v_e_1429_) == 8)
{
lean_object* v_declName_1433_; lean_object* v_type_1434_; lean_object* v_value_1435_; lean_object* v_body_1436_; uint8_t v_nondep_1437_; uint8_t v___y_1439_; uint8_t v___x_1446_; 
v_declName_1433_ = lean_ctor_get(v_e_1429_, 0);
v_type_1434_ = lean_ctor_get(v_e_1429_, 1);
v_value_1435_ = lean_ctor_get(v_e_1429_, 2);
v_body_1436_ = lean_ctor_get(v_e_1429_, 3);
v_nondep_1437_ = lean_ctor_get_uint8(v_e_1429_, sizeof(void*)*4 + 8);
v___x_1446_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_type_1434_, v_newType_1430_);
if (v___x_1446_ == 0)
{
v___y_1439_ = v___x_1446_;
goto v___jp_1438_;
}
else
{
uint8_t v___x_1447_; 
v___x_1447_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_value_1435_, v_newVal_1431_);
v___y_1439_ = v___x_1447_;
goto v___jp_1438_;
}
v___jp_1438_:
{
if (v___y_1439_ == 0)
{
lean_object* v___x_1440_; 
lean_inc(v_declName_1433_);
lean_dec_ref_known(v_e_1429_, 4);
v___x_1440_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1427_, v_inst_1428_, v_declName_1433_, v_newType_1430_, v_newVal_1431_, v_newBody_1432_, v_nondep_1437_);
return v___x_1440_;
}
else
{
uint8_t v___x_1441_; 
v___x_1441_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1436_, v_newBody_1432_);
if (v___x_1441_ == 0)
{
lean_object* v___x_1442_; 
lean_inc(v_declName_1433_);
lean_dec_ref_known(v_e_1429_, 4);
v___x_1442_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1427_, v_inst_1428_, v_declName_1433_, v_newType_1430_, v_newVal_1431_, v_newBody_1432_, v_nondep_1437_);
return v___x_1442_;
}
else
{
lean_object* v_toApplicative_1443_; lean_object* v_toPure_1444_; lean_object* v___x_1445_; 
lean_dec_ref(v_newBody_1432_);
lean_dec_ref(v_newVal_1431_);
lean_dec_ref(v_newType_1430_);
lean_dec_ref(v_inst_1427_);
v_toApplicative_1443_ = lean_ctor_get(v_inst_1428_, 0);
lean_inc_ref(v_toApplicative_1443_);
lean_dec_ref(v_inst_1428_);
v_toPure_1444_ = lean_ctor_get(v_toApplicative_1443_, 1);
lean_inc(v_toPure_1444_);
lean_dec_ref(v_toApplicative_1443_);
v___x_1445_ = lean_apply_2(v_toPure_1444_, lean_box(0), v_e_1429_);
return v___x_1445_;
}
}
}
}
else
{
lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; 
lean_dec_ref(v_newBody_1432_);
lean_dec_ref(v_newVal_1431_);
lean_dec_ref(v_newType_1430_);
lean_dec_ref(v_e_1429_);
lean_dec_ref(v_inst_1427_);
v___x_1448_ = l_Lean_instInhabitedExpr;
v___x_1449_ = l_instInhabitedOfMonad___redArg(v_inst_1428_, v___x_1448_);
v___x_1450_ = lean_obj_once(&l_Lean_Expr_updateLetS_x21___redArg___closed__2, &l_Lean_Expr_updateLetS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateLetS_x21___redArg___closed__2);
v___x_1451_ = l_panic___redArg(v___x_1449_, v___x_1450_);
lean_dec(v___x_1449_);
return v___x_1451_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLetS_x21(lean_object* v_m_1452_, lean_object* v_inst_1453_, lean_object* v_inst_1454_, lean_object* v_e_1455_, lean_object* v_newType_1456_, lean_object* v_newVal_1457_, lean_object* v_newBody_1458_){
_start:
{
if (lean_obj_tag(v_e_1455_) == 8)
{
lean_object* v_declName_1459_; lean_object* v_type_1460_; lean_object* v_value_1461_; lean_object* v_body_1462_; uint8_t v_nondep_1463_; uint8_t v___y_1465_; uint8_t v___x_1472_; 
v_declName_1459_ = lean_ctor_get(v_e_1455_, 0);
v_type_1460_ = lean_ctor_get(v_e_1455_, 1);
v_value_1461_ = lean_ctor_get(v_e_1455_, 2);
v_body_1462_ = lean_ctor_get(v_e_1455_, 3);
v_nondep_1463_ = lean_ctor_get_uint8(v_e_1455_, sizeof(void*)*4 + 8);
v___x_1472_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_type_1460_, v_newType_1456_);
if (v___x_1472_ == 0)
{
v___y_1465_ = v___x_1472_;
goto v___jp_1464_;
}
else
{
uint8_t v___x_1473_; 
v___x_1473_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_value_1461_, v_newVal_1457_);
v___y_1465_ = v___x_1473_;
goto v___jp_1464_;
}
v___jp_1464_:
{
if (v___y_1465_ == 0)
{
lean_object* v___x_1466_; 
lean_inc(v_declName_1459_);
lean_dec_ref_known(v_e_1455_, 4);
v___x_1466_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1453_, v_inst_1454_, v_declName_1459_, v_newType_1456_, v_newVal_1457_, v_newBody_1458_, v_nondep_1463_);
return v___x_1466_;
}
else
{
uint8_t v___x_1467_; 
v___x_1467_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1462_, v_newBody_1458_);
if (v___x_1467_ == 0)
{
lean_object* v___x_1468_; 
lean_inc(v_declName_1459_);
lean_dec_ref_known(v_e_1455_, 4);
v___x_1468_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1453_, v_inst_1454_, v_declName_1459_, v_newType_1456_, v_newVal_1457_, v_newBody_1458_, v_nondep_1463_);
return v___x_1468_;
}
else
{
lean_object* v_toApplicative_1469_; lean_object* v_toPure_1470_; lean_object* v___x_1471_; 
lean_dec_ref(v_newBody_1458_);
lean_dec_ref(v_newVal_1457_);
lean_dec_ref(v_newType_1456_);
lean_dec_ref(v_inst_1453_);
v_toApplicative_1469_ = lean_ctor_get(v_inst_1454_, 0);
lean_inc_ref(v_toApplicative_1469_);
lean_dec_ref(v_inst_1454_);
v_toPure_1470_ = lean_ctor_get(v_toApplicative_1469_, 1);
lean_inc(v_toPure_1470_);
lean_dec_ref(v_toApplicative_1469_);
v___x_1471_ = lean_apply_2(v_toPure_1470_, lean_box(0), v_e_1455_);
return v___x_1471_;
}
}
}
}
else
{
lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; 
lean_dec_ref(v_newBody_1458_);
lean_dec_ref(v_newVal_1457_);
lean_dec_ref(v_newType_1456_);
lean_dec_ref(v_e_1455_);
lean_dec_ref(v_inst_1453_);
v___x_1474_ = l_Lean_instInhabitedExpr;
v___x_1475_ = l_instInhabitedOfMonad___redArg(v_inst_1454_, v___x_1474_);
v___x_1476_ = lean_obj_once(&l_Lean_Expr_updateLetS_x21___redArg___closed__2, &l_Lean_Expr_updateLetS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateLetS_x21___redArg___closed__2);
v___x_1477_ = l_panic___redArg(v___x_1475_, v___x_1476_);
lean_dec(v___x_1475_);
return v___x_1477_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___redArg___lam__0(lean_object* v_inst_1478_, lean_object* v_inst_1479_, lean_object* v_a_u2082_1480_, lean_object* v_____do__lift_1481_){
_start:
{
lean_object* v___x_1482_; 
v___x_1482_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1478_, v_inst_1479_, v_____do__lift_1481_, v_a_u2082_1480_);
return v___x_1482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___redArg(lean_object* v_inst_1483_, lean_object* v_inst_1484_, lean_object* v_f_1485_, lean_object* v_a_u2081_1486_, lean_object* v_a_u2082_1487_){
_start:
{
lean_object* v_toBind_1488_; lean_object* v___f_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; 
v_toBind_1488_ = lean_ctor_get(v_inst_1484_, 1);
lean_inc(v_toBind_1488_);
lean_inc_ref(v_inst_1484_);
lean_inc_ref(v_inst_1483_);
v___f_1489_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2082___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1489_, 0, v_inst_1483_);
lean_closure_set(v___f_1489_, 1, v_inst_1484_);
lean_closure_set(v___f_1489_, 2, v_a_u2082_1487_);
v___x_1490_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1483_, v_inst_1484_, v_f_1485_, v_a_u2081_1486_);
v___x_1491_ = lean_apply_4(v_toBind_1488_, lean_box(0), lean_box(0), v___x_1490_, v___f_1489_);
return v___x_1491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082(lean_object* v_m_1492_, lean_object* v_inst_1493_, lean_object* v_inst_1494_, lean_object* v_f_1495_, lean_object* v_a_u2081_1496_, lean_object* v_a_u2082_1497_){
_start:
{
lean_object* v___x_1498_; 
v___x_1498_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___redArg(v_inst_1493_, v_inst_1494_, v_f_1495_, v_a_u2081_1496_, v_a_u2082_1497_);
return v___x_1498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___redArg___lam__0(lean_object* v_inst_1499_, lean_object* v_inst_1500_, lean_object* v_a_u2083_1501_, lean_object* v_____do__lift_1502_){
_start:
{
lean_object* v___x_1503_; 
v___x_1503_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1499_, v_inst_1500_, v_____do__lift_1502_, v_a_u2083_1501_);
return v___x_1503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___redArg(lean_object* v_inst_1504_, lean_object* v_inst_1505_, lean_object* v_f_1506_, lean_object* v_a_u2081_1507_, lean_object* v_a_u2082_1508_, lean_object* v_a_u2083_1509_){
_start:
{
lean_object* v_toBind_1510_; lean_object* v___f_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; 
v_toBind_1510_ = lean_ctor_get(v_inst_1505_, 1);
lean_inc(v_toBind_1510_);
lean_inc_ref(v_inst_1505_);
lean_inc_ref(v_inst_1504_);
v___f_1511_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2083___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1511_, 0, v_inst_1504_);
lean_closure_set(v___f_1511_, 1, v_inst_1505_);
lean_closure_set(v___f_1511_, 2, v_a_u2083_1509_);
v___x_1512_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___redArg(v_inst_1504_, v_inst_1505_, v_f_1506_, v_a_u2081_1507_, v_a_u2082_1508_);
v___x_1513_ = lean_apply_4(v_toBind_1510_, lean_box(0), lean_box(0), v___x_1512_, v___f_1511_);
return v___x_1513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083(lean_object* v_m_1514_, lean_object* v_inst_1515_, lean_object* v_inst_1516_, lean_object* v_f_1517_, lean_object* v_a_u2081_1518_, lean_object* v_a_u2082_1519_, lean_object* v_a_u2083_1520_){
_start:
{
lean_object* v___x_1521_; 
v___x_1521_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___redArg(v_inst_1515_, v_inst_1516_, v_f_1517_, v_a_u2081_1518_, v_a_u2082_1519_, v_a_u2083_1520_);
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___redArg___lam__0(lean_object* v_inst_1522_, lean_object* v_inst_1523_, lean_object* v_a_u2084_1524_, lean_object* v_____do__lift_1525_){
_start:
{
lean_object* v___x_1526_; 
v___x_1526_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1522_, v_inst_1523_, v_____do__lift_1525_, v_a_u2084_1524_);
return v___x_1526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___redArg(lean_object* v_inst_1527_, lean_object* v_inst_1528_, lean_object* v_f_1529_, lean_object* v_a_u2081_1530_, lean_object* v_a_u2082_1531_, lean_object* v_a_u2083_1532_, lean_object* v_a_u2084_1533_){
_start:
{
lean_object* v_toBind_1534_; lean_object* v___f_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; 
v_toBind_1534_ = lean_ctor_get(v_inst_1528_, 1);
lean_inc(v_toBind_1534_);
lean_inc_ref(v_inst_1528_);
lean_inc_ref(v_inst_1527_);
v___f_1535_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2084___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1535_, 0, v_inst_1527_);
lean_closure_set(v___f_1535_, 1, v_inst_1528_);
lean_closure_set(v___f_1535_, 2, v_a_u2084_1533_);
v___x_1536_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___redArg(v_inst_1527_, v_inst_1528_, v_f_1529_, v_a_u2081_1530_, v_a_u2082_1531_, v_a_u2083_1532_);
v___x_1537_ = lean_apply_4(v_toBind_1534_, lean_box(0), lean_box(0), v___x_1536_, v___f_1535_);
return v___x_1537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084(lean_object* v_m_1538_, lean_object* v_inst_1539_, lean_object* v_inst_1540_, lean_object* v_f_1541_, lean_object* v_a_u2081_1542_, lean_object* v_a_u2082_1543_, lean_object* v_a_u2083_1544_, lean_object* v_a_u2084_1545_){
_start:
{
lean_object* v___x_1546_; 
v___x_1546_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___redArg(v_inst_1539_, v_inst_1540_, v_f_1541_, v_a_u2081_1542_, v_a_u2082_1543_, v_a_u2083_1544_, v_a_u2084_1545_);
return v___x_1546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2085___redArg___lam__0(lean_object* v_inst_1547_, lean_object* v_inst_1548_, lean_object* v_a_u2085_1549_, lean_object* v_____do__lift_1550_){
_start:
{
lean_object* v___x_1551_; 
v___x_1551_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1547_, v_inst_1548_, v_____do__lift_1550_, v_a_u2085_1549_);
return v___x_1551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2085___redArg(lean_object* v_inst_1552_, lean_object* v_inst_1553_, lean_object* v_f_1554_, lean_object* v_a_u2081_1555_, lean_object* v_a_u2082_1556_, lean_object* v_a_u2083_1557_, lean_object* v_a_u2084_1558_, lean_object* v_a_u2085_1559_){
_start:
{
lean_object* v_toBind_1560_; lean_object* v___f_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; 
v_toBind_1560_ = lean_ctor_get(v_inst_1553_, 1);
lean_inc(v_toBind_1560_);
lean_inc_ref(v_inst_1553_);
lean_inc_ref(v_inst_1552_);
v___f_1561_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2085___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1561_, 0, v_inst_1552_);
lean_closure_set(v___f_1561_, 1, v_inst_1553_);
lean_closure_set(v___f_1561_, 2, v_a_u2085_1559_);
v___x_1562_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___redArg(v_inst_1552_, v_inst_1553_, v_f_1554_, v_a_u2081_1555_, v_a_u2082_1556_, v_a_u2083_1557_, v_a_u2084_1558_);
v___x_1563_ = lean_apply_4(v_toBind_1560_, lean_box(0), lean_box(0), v___x_1562_, v___f_1561_);
return v___x_1563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2085(lean_object* v_m_1564_, lean_object* v_inst_1565_, lean_object* v_inst_1566_, lean_object* v_f_1567_, lean_object* v_a_u2081_1568_, lean_object* v_a_u2082_1569_, lean_object* v_a_u2083_1570_, lean_object* v_a_u2084_1571_, lean_object* v_a_u2085_1572_){
_start:
{
lean_object* v___x_1573_; 
v___x_1573_ = l_Lean_Meta_Sym_Internal_mkAppS_u2085___redArg(v_inst_1565_, v_inst_1566_, v_f_1567_, v_a_u2081_1568_, v_a_u2082_1569_, v_a_u2083_1570_, v_a_u2084_1571_, v_a_u2085_1572_);
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2086___redArg___lam__0(lean_object* v_inst_1574_, lean_object* v_inst_1575_, lean_object* v_a_u2086_1576_, lean_object* v_____do__lift_1577_){
_start:
{
lean_object* v___x_1578_; 
v___x_1578_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1574_, v_inst_1575_, v_____do__lift_1577_, v_a_u2086_1576_);
return v___x_1578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2086___redArg(lean_object* v_inst_1579_, lean_object* v_inst_1580_, lean_object* v_f_1581_, lean_object* v_a_u2081_1582_, lean_object* v_a_u2082_1583_, lean_object* v_a_u2083_1584_, lean_object* v_a_u2084_1585_, lean_object* v_a_u2085_1586_, lean_object* v_a_u2086_1587_){
_start:
{
lean_object* v_toBind_1588_; lean_object* v___f_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; 
v_toBind_1588_ = lean_ctor_get(v_inst_1580_, 1);
lean_inc(v_toBind_1588_);
lean_inc_ref(v_inst_1580_);
lean_inc_ref(v_inst_1579_);
v___f_1589_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2086___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1589_, 0, v_inst_1579_);
lean_closure_set(v___f_1589_, 1, v_inst_1580_);
lean_closure_set(v___f_1589_, 2, v_a_u2086_1587_);
v___x_1590_ = l_Lean_Meta_Sym_Internal_mkAppS_u2085___redArg(v_inst_1579_, v_inst_1580_, v_f_1581_, v_a_u2081_1582_, v_a_u2082_1583_, v_a_u2083_1584_, v_a_u2084_1585_, v_a_u2085_1586_);
v___x_1591_ = lean_apply_4(v_toBind_1588_, lean_box(0), lean_box(0), v___x_1590_, v___f_1589_);
return v___x_1591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2086(lean_object* v_m_1592_, lean_object* v_inst_1593_, lean_object* v_inst_1594_, lean_object* v_f_1595_, lean_object* v_a_u2081_1596_, lean_object* v_a_u2082_1597_, lean_object* v_a_u2083_1598_, lean_object* v_a_u2084_1599_, lean_object* v_a_u2085_1600_, lean_object* v_a_u2086_1601_){
_start:
{
lean_object* v___x_1602_; 
v___x_1602_ = l_Lean_Meta_Sym_Internal_mkAppS_u2086___redArg(v_inst_1593_, v_inst_1594_, v_f_1595_, v_a_u2081_1596_, v_a_u2082_1597_, v_a_u2083_1598_, v_a_u2084_1599_, v_a_u2085_1600_, v_a_u2086_1601_);
return v___x_1602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2087___redArg___lam__0(lean_object* v_inst_1603_, lean_object* v_inst_1604_, lean_object* v_a_u2087_1605_, lean_object* v_____do__lift_1606_){
_start:
{
lean_object* v___x_1607_; 
v___x_1607_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1603_, v_inst_1604_, v_____do__lift_1606_, v_a_u2087_1605_);
return v___x_1607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2087___redArg(lean_object* v_inst_1608_, lean_object* v_inst_1609_, lean_object* v_f_1610_, lean_object* v_a_u2081_1611_, lean_object* v_a_u2082_1612_, lean_object* v_a_u2083_1613_, lean_object* v_a_u2084_1614_, lean_object* v_a_u2085_1615_, lean_object* v_a_u2086_1616_, lean_object* v_a_u2087_1617_){
_start:
{
lean_object* v_toBind_1618_; lean_object* v___f_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; 
v_toBind_1618_ = lean_ctor_get(v_inst_1609_, 1);
lean_inc(v_toBind_1618_);
lean_inc_ref(v_inst_1609_);
lean_inc_ref(v_inst_1608_);
v___f_1619_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2087___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1619_, 0, v_inst_1608_);
lean_closure_set(v___f_1619_, 1, v_inst_1609_);
lean_closure_set(v___f_1619_, 2, v_a_u2087_1617_);
v___x_1620_ = l_Lean_Meta_Sym_Internal_mkAppS_u2086___redArg(v_inst_1608_, v_inst_1609_, v_f_1610_, v_a_u2081_1611_, v_a_u2082_1612_, v_a_u2083_1613_, v_a_u2084_1614_, v_a_u2085_1615_, v_a_u2086_1616_);
v___x_1621_ = lean_apply_4(v_toBind_1618_, lean_box(0), lean_box(0), v___x_1620_, v___f_1619_);
return v___x_1621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2087(lean_object* v_m_1622_, lean_object* v_inst_1623_, lean_object* v_inst_1624_, lean_object* v_f_1625_, lean_object* v_a_u2081_1626_, lean_object* v_a_u2082_1627_, lean_object* v_a_u2083_1628_, lean_object* v_a_u2084_1629_, lean_object* v_a_u2085_1630_, lean_object* v_a_u2086_1631_, lean_object* v_a_u2087_1632_){
_start:
{
lean_object* v___x_1633_; 
v___x_1633_ = l_Lean_Meta_Sym_Internal_mkAppS_u2087___redArg(v_inst_1623_, v_inst_1624_, v_f_1625_, v_a_u2081_1626_, v_a_u2082_1627_, v_a_u2083_1628_, v_a_u2084_1629_, v_a_u2085_1630_, v_a_u2086_1631_, v_a_u2087_1632_);
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2088___redArg___lam__0(lean_object* v_inst_1634_, lean_object* v_inst_1635_, lean_object* v_a_u2088_1636_, lean_object* v_____do__lift_1637_){
_start:
{
lean_object* v___x_1638_; 
v___x_1638_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1634_, v_inst_1635_, v_____do__lift_1637_, v_a_u2088_1636_);
return v___x_1638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2088___redArg(lean_object* v_inst_1639_, lean_object* v_inst_1640_, lean_object* v_f_1641_, lean_object* v_a_u2081_1642_, lean_object* v_a_u2082_1643_, lean_object* v_a_u2083_1644_, lean_object* v_a_u2084_1645_, lean_object* v_a_u2085_1646_, lean_object* v_a_u2086_1647_, lean_object* v_a_u2087_1648_, lean_object* v_a_u2088_1649_){
_start:
{
lean_object* v_toBind_1650_; lean_object* v___f_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; 
v_toBind_1650_ = lean_ctor_get(v_inst_1640_, 1);
lean_inc(v_toBind_1650_);
lean_inc_ref(v_inst_1640_);
lean_inc_ref(v_inst_1639_);
v___f_1651_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2088___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1651_, 0, v_inst_1639_);
lean_closure_set(v___f_1651_, 1, v_inst_1640_);
lean_closure_set(v___f_1651_, 2, v_a_u2088_1649_);
v___x_1652_ = l_Lean_Meta_Sym_Internal_mkAppS_u2087___redArg(v_inst_1639_, v_inst_1640_, v_f_1641_, v_a_u2081_1642_, v_a_u2082_1643_, v_a_u2083_1644_, v_a_u2084_1645_, v_a_u2085_1646_, v_a_u2086_1647_, v_a_u2087_1648_);
v___x_1653_ = lean_apply_4(v_toBind_1650_, lean_box(0), lean_box(0), v___x_1652_, v___f_1651_);
return v___x_1653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2088(lean_object* v_m_1654_, lean_object* v_inst_1655_, lean_object* v_inst_1656_, lean_object* v_f_1657_, lean_object* v_a_u2081_1658_, lean_object* v_a_u2082_1659_, lean_object* v_a_u2083_1660_, lean_object* v_a_u2084_1661_, lean_object* v_a_u2085_1662_, lean_object* v_a_u2086_1663_, lean_object* v_a_u2087_1664_, lean_object* v_a_u2088_1665_){
_start:
{
lean_object* v___x_1666_; 
v___x_1666_ = l_Lean_Meta_Sym_Internal_mkAppS_u2088___redArg(v_inst_1655_, v_inst_1656_, v_f_1657_, v_a_u2081_1658_, v_a_u2082_1659_, v_a_u2083_1660_, v_a_u2084_1661_, v_a_u2085_1662_, v_a_u2086_1663_, v_a_u2087_1664_, v_a_u2088_1665_);
return v___x_1666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2089___redArg___lam__0(lean_object* v_inst_1667_, lean_object* v_inst_1668_, lean_object* v_a_u2089_1669_, lean_object* v_____do__lift_1670_){
_start:
{
lean_object* v___x_1671_; 
v___x_1671_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1667_, v_inst_1668_, v_____do__lift_1670_, v_a_u2089_1669_);
return v___x_1671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2089___redArg(lean_object* v_inst_1672_, lean_object* v_inst_1673_, lean_object* v_f_1674_, lean_object* v_a_u2081_1675_, lean_object* v_a_u2082_1676_, lean_object* v_a_u2083_1677_, lean_object* v_a_u2084_1678_, lean_object* v_a_u2085_1679_, lean_object* v_a_u2086_1680_, lean_object* v_a_u2087_1681_, lean_object* v_a_u2088_1682_, lean_object* v_a_u2089_1683_){
_start:
{
lean_object* v_toBind_1684_; lean_object* v___f_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; 
v_toBind_1684_ = lean_ctor_get(v_inst_1673_, 1);
lean_inc(v_toBind_1684_);
lean_inc_ref(v_inst_1673_);
lean_inc_ref(v_inst_1672_);
v___f_1685_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2089___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1685_, 0, v_inst_1672_);
lean_closure_set(v___f_1685_, 1, v_inst_1673_);
lean_closure_set(v___f_1685_, 2, v_a_u2089_1683_);
v___x_1686_ = l_Lean_Meta_Sym_Internal_mkAppS_u2088___redArg(v_inst_1672_, v_inst_1673_, v_f_1674_, v_a_u2081_1675_, v_a_u2082_1676_, v_a_u2083_1677_, v_a_u2084_1678_, v_a_u2085_1679_, v_a_u2086_1680_, v_a_u2087_1681_, v_a_u2088_1682_);
v___x_1687_ = lean_apply_4(v_toBind_1684_, lean_box(0), lean_box(0), v___x_1686_, v___f_1685_);
return v___x_1687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2089(lean_object* v_m_1688_, lean_object* v_inst_1689_, lean_object* v_inst_1690_, lean_object* v_f_1691_, lean_object* v_a_u2081_1692_, lean_object* v_a_u2082_1693_, lean_object* v_a_u2083_1694_, lean_object* v_a_u2084_1695_, lean_object* v_a_u2085_1696_, lean_object* v_a_u2086_1697_, lean_object* v_a_u2087_1698_, lean_object* v_a_u2088_1699_, lean_object* v_a_u2089_1700_){
_start:
{
lean_object* v___x_1701_; 
v___x_1701_ = l_Lean_Meta_Sym_Internal_mkAppS_u2089___redArg(v_inst_1689_, v_inst_1690_, v_f_1691_, v_a_u2081_1692_, v_a_u2082_1693_, v_a_u2083_1694_, v_a_u2084_1695_, v_a_u2085_1696_, v_a_u2086_1697_, v_a_u2087_1698_, v_a_u2088_1699_, v_a_u2089_1700_);
return v___x_1701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2080___redArg___lam__0(lean_object* v_inst_1702_, lean_object* v_inst_1703_, lean_object* v_a_u2081_u2080_1704_, lean_object* v_____do__lift_1705_){
_start:
{
lean_object* v___x_1706_; 
v___x_1706_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1702_, v_inst_1703_, v_____do__lift_1705_, v_a_u2081_u2080_1704_);
return v___x_1706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2080___redArg(lean_object* v_inst_1707_, lean_object* v_inst_1708_, lean_object* v_f_1709_, lean_object* v_a_u2081_1710_, lean_object* v_a_u2082_1711_, lean_object* v_a_u2083_1712_, lean_object* v_a_u2084_1713_, lean_object* v_a_u2085_1714_, lean_object* v_a_u2086_1715_, lean_object* v_a_u2087_1716_, lean_object* v_a_u2088_1717_, lean_object* v_a_u2089_1718_, lean_object* v_a_u2081_u2080_1719_){
_start:
{
lean_object* v_toBind_1720_; lean_object* v___f_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; 
v_toBind_1720_ = lean_ctor_get(v_inst_1708_, 1);
lean_inc(v_toBind_1720_);
lean_inc_ref(v_inst_1708_);
lean_inc_ref(v_inst_1707_);
v___f_1721_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2080___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1721_, 0, v_inst_1707_);
lean_closure_set(v___f_1721_, 1, v_inst_1708_);
lean_closure_set(v___f_1721_, 2, v_a_u2081_u2080_1719_);
v___x_1722_ = l_Lean_Meta_Sym_Internal_mkAppS_u2089___redArg(v_inst_1707_, v_inst_1708_, v_f_1709_, v_a_u2081_1710_, v_a_u2082_1711_, v_a_u2083_1712_, v_a_u2084_1713_, v_a_u2085_1714_, v_a_u2086_1715_, v_a_u2087_1716_, v_a_u2088_1717_, v_a_u2089_1718_);
v___x_1723_ = lean_apply_4(v_toBind_1720_, lean_box(0), lean_box(0), v___x_1722_, v___f_1721_);
return v___x_1723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2080(lean_object* v_m_1724_, lean_object* v_inst_1725_, lean_object* v_inst_1726_, lean_object* v_f_1727_, lean_object* v_a_u2081_1728_, lean_object* v_a_u2082_1729_, lean_object* v_a_u2083_1730_, lean_object* v_a_u2084_1731_, lean_object* v_a_u2085_1732_, lean_object* v_a_u2086_1733_, lean_object* v_a_u2087_1734_, lean_object* v_a_u2088_1735_, lean_object* v_a_u2089_1736_, lean_object* v_a_u2081_u2080_1737_){
_start:
{
lean_object* v___x_1738_; 
v___x_1738_ = l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2080___redArg(v_inst_1725_, v_inst_1726_, v_f_1727_, v_a_u2081_1728_, v_a_u2082_1729_, v_a_u2083_1730_, v_a_u2084_1731_, v_a_u2085_1732_, v_a_u2086_1733_, v_a_u2087_1734_, v_a_u2088_1735_, v_a_u2089_1736_, v_a_u2081_u2080_1737_);
return v___x_1738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2081___redArg___lam__0(lean_object* v_inst_1739_, lean_object* v_inst_1740_, lean_object* v_a_u2081_u2081_1741_, lean_object* v_____do__lift_1742_){
_start:
{
lean_object* v___x_1743_; 
v___x_1743_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1739_, v_inst_1740_, v_____do__lift_1742_, v_a_u2081_u2081_1741_);
return v___x_1743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2081___redArg(lean_object* v_inst_1744_, lean_object* v_inst_1745_, lean_object* v_f_1746_, lean_object* v_a_u2081_1747_, lean_object* v_a_u2082_1748_, lean_object* v_a_u2083_1749_, lean_object* v_a_u2084_1750_, lean_object* v_a_u2085_1751_, lean_object* v_a_u2086_1752_, lean_object* v_a_u2087_1753_, lean_object* v_a_u2088_1754_, lean_object* v_a_u2089_1755_, lean_object* v_a_u2081_u2080_1756_, lean_object* v_a_u2081_u2081_1757_){
_start:
{
lean_object* v_toBind_1758_; lean_object* v___f_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; 
v_toBind_1758_ = lean_ctor_get(v_inst_1745_, 1);
lean_inc(v_toBind_1758_);
lean_inc_ref(v_inst_1745_);
lean_inc_ref(v_inst_1744_);
v___f_1759_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2081___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1759_, 0, v_inst_1744_);
lean_closure_set(v___f_1759_, 1, v_inst_1745_);
lean_closure_set(v___f_1759_, 2, v_a_u2081_u2081_1757_);
v___x_1760_ = l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2080___redArg(v_inst_1744_, v_inst_1745_, v_f_1746_, v_a_u2081_1747_, v_a_u2082_1748_, v_a_u2083_1749_, v_a_u2084_1750_, v_a_u2085_1751_, v_a_u2086_1752_, v_a_u2087_1753_, v_a_u2088_1754_, v_a_u2089_1755_, v_a_u2081_u2080_1756_);
v___x_1761_ = lean_apply_4(v_toBind_1758_, lean_box(0), lean_box(0), v___x_1760_, v___f_1759_);
return v___x_1761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2081(lean_object* v_m_1762_, lean_object* v_inst_1763_, lean_object* v_inst_1764_, lean_object* v_f_1765_, lean_object* v_a_u2081_1766_, lean_object* v_a_u2082_1767_, lean_object* v_a_u2083_1768_, lean_object* v_a_u2084_1769_, lean_object* v_a_u2085_1770_, lean_object* v_a_u2086_1771_, lean_object* v_a_u2087_1772_, lean_object* v_a_u2088_1773_, lean_object* v_a_u2089_1774_, lean_object* v_a_u2081_u2080_1775_, lean_object* v_a_u2081_u2081_1776_){
_start:
{
lean_object* v___x_1777_; 
v___x_1777_ = l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2081___redArg(v_inst_1763_, v_inst_1764_, v_f_1765_, v_a_u2081_1766_, v_a_u2082_1767_, v_a_u2083_1768_, v_a_u2084_1769_, v_a_u2085_1770_, v_a_u2086_1771_, v_a_u2087_1772_, v_a_u2088_1773_, v_a_u2089_1774_, v_a_u2081_u2080_1775_, v_a_u2081_u2081_1776_);
return v___x_1777_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg___lam__0___boxed(lean_object* v_i_1778_, lean_object* v_inst_1779_, lean_object* v_inst_1780_, lean_object* v_args_1781_, lean_object* v_endIdx_1782_, lean_object* v_____do__lift_1783_){
_start:
{
lean_object* v_res_1784_; 
v_res_1784_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg___lam__0(v_i_1778_, v_inst_1779_, v_inst_1780_, v_args_1781_, v_endIdx_1782_, v_____do__lift_1783_);
lean_dec(v_i_1778_);
return v_res_1784_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg(lean_object* v_inst_1785_, lean_object* v_inst_1786_, lean_object* v_args_1787_, lean_object* v_endIdx_1788_, lean_object* v_b_1789_, lean_object* v_i_1790_){
_start:
{
uint8_t v___x_1791_; 
v___x_1791_ = lean_nat_dec_le(v_endIdx_1788_, v_i_1790_);
if (v___x_1791_ == 0)
{
lean_object* v_toBind_1792_; lean_object* v___f_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; 
v_toBind_1792_ = lean_ctor_get(v_inst_1786_, 1);
lean_inc(v_toBind_1792_);
lean_inc_ref(v_args_1787_);
lean_inc_ref(v_inst_1786_);
lean_inc_ref(v_inst_1785_);
lean_inc(v_i_1790_);
v___f_1793_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1793_, 0, v_i_1790_);
lean_closure_set(v___f_1793_, 1, v_inst_1785_);
lean_closure_set(v___f_1793_, 2, v_inst_1786_);
lean_closure_set(v___f_1793_, 3, v_args_1787_);
lean_closure_set(v___f_1793_, 4, v_endIdx_1788_);
v___x_1794_ = l_Lean_instInhabitedExpr;
v___x_1795_ = lean_array_get(v___x_1794_, v_args_1787_, v_i_1790_);
lean_dec(v_i_1790_);
lean_dec_ref(v_args_1787_);
v___x_1796_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1785_, v_inst_1786_, v_b_1789_, v___x_1795_);
v___x_1797_ = lean_apply_4(v_toBind_1792_, lean_box(0), lean_box(0), v___x_1796_, v___f_1793_);
return v___x_1797_;
}
else
{
lean_object* v_toApplicative_1798_; lean_object* v_toPure_1799_; lean_object* v___x_1800_; 
lean_dec(v_i_1790_);
lean_dec(v_endIdx_1788_);
lean_dec_ref(v_args_1787_);
lean_dec_ref(v_inst_1785_);
v_toApplicative_1798_ = lean_ctor_get(v_inst_1786_, 0);
lean_inc_ref(v_toApplicative_1798_);
lean_dec_ref(v_inst_1786_);
v_toPure_1799_ = lean_ctor_get(v_toApplicative_1798_, 1);
lean_inc(v_toPure_1799_);
lean_dec_ref(v_toApplicative_1798_);
v___x_1800_ = lean_apply_2(v_toPure_1799_, lean_box(0), v_b_1789_);
return v___x_1800_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg___lam__0(lean_object* v_i_1801_, lean_object* v_inst_1802_, lean_object* v_inst_1803_, lean_object* v_args_1804_, lean_object* v_endIdx_1805_, lean_object* v_____do__lift_1806_){
_start:
{
lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; 
v___x_1807_ = lean_unsigned_to_nat(1u);
v___x_1808_ = lean_nat_add(v_i_1801_, v___x_1807_);
v___x_1809_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg(v_inst_1802_, v_inst_1803_, v_args_1804_, v_endIdx_1805_, v_____do__lift_1806_, v___x_1808_);
return v___x_1809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go(lean_object* v_m_1810_, lean_object* v_inst_1811_, lean_object* v_inst_1812_, lean_object* v_args_1813_, lean_object* v_endIdx_1814_, lean_object* v_b_1815_, lean_object* v_i_1816_){
_start:
{
lean_object* v___x_1817_; 
v___x_1817_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg(v_inst_1811_, v_inst_1812_, v_args_1813_, v_endIdx_1814_, v_b_1815_, v_i_1816_);
return v___x_1817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRangeS___redArg(lean_object* v_inst_1818_, lean_object* v_inst_1819_, lean_object* v_f_1820_, lean_object* v_beginIdx_1821_, lean_object* v_endIdx_1822_, lean_object* v_args_1823_){
_start:
{
lean_object* v___x_1824_; 
v___x_1824_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg(v_inst_1818_, v_inst_1819_, v_args_1823_, v_endIdx_1822_, v_f_1820_, v_beginIdx_1821_);
return v___x_1824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRangeS(lean_object* v_m_1825_, lean_object* v_inst_1826_, lean_object* v_inst_1827_, lean_object* v_f_1828_, lean_object* v_beginIdx_1829_, lean_object* v_endIdx_1830_, lean_object* v_args_1831_){
_start:
{
lean_object* v___x_1832_; 
v___x_1832_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg(v_inst_1826_, v_inst_1827_, v_args_1831_, v_endIdx_1830_, v_f_1828_, v_beginIdx_1829_);
return v___x_1832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___redArg(lean_object* v_inst_1833_, lean_object* v_inst_1834_, lean_object* v_f_1835_, lean_object* v_args_1836_){
_start:
{
lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; 
v___x_1837_ = lean_unsigned_to_nat(0u);
v___x_1838_ = lean_array_get_size(v_args_1836_);
v___x_1839_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg(v_inst_1833_, v_inst_1834_, v_args_1836_, v___x_1838_, v_f_1835_, v___x_1837_);
return v___x_1839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS(lean_object* v_m_1840_, lean_object* v_inst_1841_, lean_object* v_inst_1842_, lean_object* v_f_1843_, lean_object* v_args_1844_){
_start:
{
lean_object* v___x_1845_; 
v___x_1845_ = l_Lean_Meta_Sym_Internal_mkAppNS___redArg(v_inst_1841_, v_inst_1842_, v_f_1843_, v_args_1844_);
return v___x_1845_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg___lam__0___boxed(lean_object* v_inst_1846_, lean_object* v_inst_1847_, lean_object* v_revArgs_1848_, lean_object* v_start_1849_, lean_object* v_i_1850_, lean_object* v_____do__lift_1851_){
_start:
{
lean_object* v_res_1852_; 
v_res_1852_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg___lam__0(v_inst_1846_, v_inst_1847_, v_revArgs_1848_, v_start_1849_, v_i_1850_, v_____do__lift_1851_);
lean_dec(v_i_1850_);
return v_res_1852_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg(lean_object* v_inst_1853_, lean_object* v_inst_1854_, lean_object* v_revArgs_1855_, lean_object* v_start_1856_, lean_object* v_b_1857_, lean_object* v_i_1858_){
_start:
{
uint8_t v___x_1859_; 
v___x_1859_ = lean_nat_dec_le(v_i_1858_, v_start_1856_);
if (v___x_1859_ == 0)
{
lean_object* v_toBind_1860_; lean_object* v___x_1861_; lean_object* v_i_1862_; lean_object* v___f_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; 
v_toBind_1860_ = lean_ctor_get(v_inst_1854_, 1);
lean_inc(v_toBind_1860_);
v___x_1861_ = lean_unsigned_to_nat(1u);
v_i_1862_ = lean_nat_sub(v_i_1858_, v___x_1861_);
lean_inc(v_i_1862_);
lean_inc_ref(v_revArgs_1855_);
lean_inc_ref(v_inst_1854_);
lean_inc_ref(v_inst_1853_);
v___f_1863_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1863_, 0, v_inst_1853_);
lean_closure_set(v___f_1863_, 1, v_inst_1854_);
lean_closure_set(v___f_1863_, 2, v_revArgs_1855_);
lean_closure_set(v___f_1863_, 3, v_start_1856_);
lean_closure_set(v___f_1863_, 4, v_i_1862_);
v___x_1864_ = l_Lean_instInhabitedExpr;
v___x_1865_ = lean_array_get(v___x_1864_, v_revArgs_1855_, v_i_1862_);
lean_dec(v_i_1862_);
lean_dec_ref(v_revArgs_1855_);
v___x_1866_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1853_, v_inst_1854_, v_b_1857_, v___x_1865_);
v___x_1867_ = lean_apply_4(v_toBind_1860_, lean_box(0), lean_box(0), v___x_1866_, v___f_1863_);
return v___x_1867_;
}
else
{
lean_object* v_toApplicative_1868_; lean_object* v_toPure_1869_; lean_object* v___x_1870_; 
lean_dec(v_start_1856_);
lean_dec_ref(v_revArgs_1855_);
lean_dec_ref(v_inst_1853_);
v_toApplicative_1868_ = lean_ctor_get(v_inst_1854_, 0);
lean_inc_ref(v_toApplicative_1868_);
lean_dec_ref(v_inst_1854_);
v_toPure_1869_ = lean_ctor_get(v_toApplicative_1868_, 1);
lean_inc(v_toPure_1869_);
lean_dec_ref(v_toApplicative_1868_);
v___x_1870_ = lean_apply_2(v_toPure_1869_, lean_box(0), v_b_1857_);
return v___x_1870_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg___lam__0(lean_object* v_inst_1871_, lean_object* v_inst_1872_, lean_object* v_revArgs_1873_, lean_object* v_start_1874_, lean_object* v_i_1875_, lean_object* v_____do__lift_1876_){
_start:
{
lean_object* v___x_1877_; 
v___x_1877_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg(v_inst_1871_, v_inst_1872_, v_revArgs_1873_, v_start_1874_, v_____do__lift_1876_, v_i_1875_);
return v___x_1877_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg___boxed(lean_object* v_inst_1878_, lean_object* v_inst_1879_, lean_object* v_revArgs_1880_, lean_object* v_start_1881_, lean_object* v_b_1882_, lean_object* v_i_1883_){
_start:
{
lean_object* v_res_1884_; 
v_res_1884_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg(v_inst_1878_, v_inst_1879_, v_revArgs_1880_, v_start_1881_, v_b_1882_, v_i_1883_);
lean_dec(v_i_1883_);
return v_res_1884_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go(lean_object* v_m_1885_, lean_object* v_inst_1886_, lean_object* v_inst_1887_, lean_object* v_revArgs_1888_, lean_object* v_start_1889_, lean_object* v_b_1890_, lean_object* v_i_1891_){
_start:
{
lean_object* v___x_1892_; 
v___x_1892_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg(v_inst_1886_, v_inst_1887_, v_revArgs_1888_, v_start_1889_, v_b_1890_, v_i_1891_);
return v___x_1892_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___boxed(lean_object* v_m_1893_, lean_object* v_inst_1894_, lean_object* v_inst_1895_, lean_object* v_revArgs_1896_, lean_object* v_start_1897_, lean_object* v_b_1898_, lean_object* v_i_1899_){
_start:
{
lean_object* v_res_1900_; 
v_res_1900_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go(v_m_1893_, v_inst_1894_, v_inst_1895_, v_revArgs_1896_, v_start_1897_, v_b_1898_, v_i_1899_);
lean_dec(v_i_1899_);
return v_res_1900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevRangeS___redArg(lean_object* v_inst_1901_, lean_object* v_inst_1902_, lean_object* v_f_1903_, lean_object* v_beginIdx_1904_, lean_object* v_endIdx_1905_, lean_object* v_revArgs_1906_){
_start:
{
lean_object* v___x_1907_; 
v___x_1907_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg(v_inst_1901_, v_inst_1902_, v_revArgs_1906_, v_beginIdx_1904_, v_f_1903_, v_endIdx_1905_);
return v___x_1907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevRangeS___redArg___boxed(lean_object* v_inst_1908_, lean_object* v_inst_1909_, lean_object* v_f_1910_, lean_object* v_beginIdx_1911_, lean_object* v_endIdx_1912_, lean_object* v_revArgs_1913_){
_start:
{
lean_object* v_res_1914_; 
v_res_1914_ = l_Lean_Meta_Sym_Internal_mkAppRevRangeS___redArg(v_inst_1908_, v_inst_1909_, v_f_1910_, v_beginIdx_1911_, v_endIdx_1912_, v_revArgs_1913_);
lean_dec(v_endIdx_1912_);
return v_res_1914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevRangeS(lean_object* v_m_1915_, lean_object* v_inst_1916_, lean_object* v_inst_1917_, lean_object* v_f_1918_, lean_object* v_beginIdx_1919_, lean_object* v_endIdx_1920_, lean_object* v_revArgs_1921_){
_start:
{
lean_object* v___x_1922_; 
v___x_1922_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg(v_inst_1916_, v_inst_1917_, v_revArgs_1921_, v_beginIdx_1919_, v_f_1918_, v_endIdx_1920_);
return v___x_1922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevRangeS___boxed(lean_object* v_m_1923_, lean_object* v_inst_1924_, lean_object* v_inst_1925_, lean_object* v_f_1926_, lean_object* v_beginIdx_1927_, lean_object* v_endIdx_1928_, lean_object* v_revArgs_1929_){
_start:
{
lean_object* v_res_1930_; 
v_res_1930_ = l_Lean_Meta_Sym_Internal_mkAppRevRangeS(v_m_1923_, v_inst_1924_, v_inst_1925_, v_f_1926_, v_beginIdx_1927_, v_endIdx_1928_, v_revArgs_1929_);
lean_dec(v_endIdx_1928_);
return v_res_1930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevS___redArg(lean_object* v_inst_1931_, lean_object* v_inst_1932_, lean_object* v_f_1933_, lean_object* v_revArgs_1934_){
_start:
{
lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; 
v___x_1935_ = lean_unsigned_to_nat(0u);
v___x_1936_ = lean_array_get_size(v_revArgs_1934_);
v___x_1937_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg(v_inst_1931_, v_inst_1932_, v_revArgs_1934_, v___x_1935_, v_f_1933_, v___x_1936_);
return v___x_1937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevS(lean_object* v_m_1938_, lean_object* v_inst_1939_, lean_object* v_inst_1940_, lean_object* v_f_1941_, lean_object* v_revArgs_1942_){
_start:
{
lean_object* v___x_1943_; 
v___x_1943_ = l_Lean_Meta_Sym_Internal_mkAppRevS___redArg(v_inst_1939_, v_inst_1940_, v_f_1941_, v_revArgs_1942_);
return v___x_1943_;
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
