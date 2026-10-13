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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
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
lean_object* l_Std_HashMap_instInhabited___redArg();
lean_object* l_EStateM_instInhabited___redArg___lam__0(lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg();
lean_object* l_Lean_Meta_Sym_runShareCommonM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_EStateM_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_seqRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Lean.Meta.Sym.Internal.liftBuilderM"};
static const lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__0_value;
static const lean_string_object l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_share1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_share1(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_share1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__0;
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
static const lean_closure_object l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonad___redArg___lam__0, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__0_value;
static const lean_closure_object l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonad___redArg___lam__1, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__1_value;
static const lean_closure_object l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonad___redArg___lam__2, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
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
v___x_85_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
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
size_t v_x_2079__boxed_189_; size_t v_x_2080__boxed_190_; lean_object* v_res_191_; 
v_x_2079__boxed_189_ = lean_unbox_usize(v_x_185_);
lean_dec(v_x_185_);
v_x_2080__boxed_190_ = lean_unbox_usize(v_x_186_);
lean_dec(v_x_186_);
v_res_191_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg(v_x_184_, v_x_2079__boxed_189_, v_x_2080__boxed_190_, v_x_187_, v_x_188_);
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
size_t v_x_2257__boxed_238_; lean_object* v_res_239_; 
v_x_2257__boxed_238_ = lean_unbox_usize(v_x_235_);
lean_dec(v_x_235_);
v_res_239_ = l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg(v_x_234_, v_x_2257__boxed_238_, v_x_236_, v_x_237_);
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
lean_object* v___x_255_; lean_object* v_share_256_; lean_object* v_maxFVar_257_; lean_object* v_proofInstInfo_258_; lean_object* v_proofInstInfoFVar_259_; lean_object* v_inferType_260_; lean_object* v_getLevel_261_; lean_object* v_congrInfo_262_; lean_object* v_defEqI_263_; lean_object* v_extensions_264_; lean_object* v_issues_265_; lean_object* v_canon_266_; lean_object* v_instanceOverrides_267_; uint8_t v_debug_268_; lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_279_; 
lean_dec_ref(v___x_250_);
v___x_255_ = lean_st_ref_take(v_a_243_);
v_share_256_ = lean_ctor_get(v___x_255_, 0);
v_maxFVar_257_ = lean_ctor_get(v___x_255_, 1);
v_proofInstInfo_258_ = lean_ctor_get(v___x_255_, 2);
v_proofInstInfoFVar_259_ = lean_ctor_get(v___x_255_, 3);
v_inferType_260_ = lean_ctor_get(v___x_255_, 4);
v_getLevel_261_ = lean_ctor_get(v___x_255_, 5);
v_congrInfo_262_ = lean_ctor_get(v___x_255_, 6);
v_defEqI_263_ = lean_ctor_get(v___x_255_, 7);
v_extensions_264_ = lean_ctor_get(v___x_255_, 8);
v_issues_265_ = lean_ctor_get(v___x_255_, 9);
v_canon_266_ = lean_ctor_get(v___x_255_, 10);
v_instanceOverrides_267_ = lean_ctor_get(v___x_255_, 11);
v_debug_268_ = lean_ctor_get_uint8(v___x_255_, sizeof(void*)*12);
v_isSharedCheck_279_ = !lean_is_exclusive(v___x_255_);
if (v_isSharedCheck_279_ == 0)
{
v___x_270_ = v___x_255_;
v_isShared_271_ = v_isSharedCheck_279_;
goto v_resetjp_269_;
}
else
{
lean_inc(v_instanceOverrides_267_);
lean_inc(v_canon_266_);
lean_inc(v_issues_265_);
lean_inc(v_extensions_264_);
lean_inc(v_defEqI_263_);
lean_inc(v_congrInfo_262_);
lean_inc(v_getLevel_261_);
lean_inc(v_inferType_260_);
lean_inc(v_proofInstInfoFVar_259_);
lean_inc(v_proofInstInfo_258_);
lean_inc(v_maxFVar_257_);
lean_inc(v_share_256_);
lean_dec(v___x_255_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_279_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_275_; 
v___x_272_ = lean_box(0);
lean_inc_ref(v_e_242_);
v___x_273_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1___redArg(v_share_256_, v_e_242_, v___x_272_);
if (v_isShared_271_ == 0)
{
lean_ctor_set(v___x_270_, 0, v___x_273_);
v___x_275_ = v___x_270_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v___x_273_);
lean_ctor_set(v_reuseFailAlloc_278_, 1, v_maxFVar_257_);
lean_ctor_set(v_reuseFailAlloc_278_, 2, v_proofInstInfo_258_);
lean_ctor_set(v_reuseFailAlloc_278_, 3, v_proofInstInfoFVar_259_);
lean_ctor_set(v_reuseFailAlloc_278_, 4, v_inferType_260_);
lean_ctor_set(v_reuseFailAlloc_278_, 5, v_getLevel_261_);
lean_ctor_set(v_reuseFailAlloc_278_, 6, v_congrInfo_262_);
lean_ctor_set(v_reuseFailAlloc_278_, 7, v_defEqI_263_);
lean_ctor_set(v_reuseFailAlloc_278_, 8, v_extensions_264_);
lean_ctor_set(v_reuseFailAlloc_278_, 9, v_issues_265_);
lean_ctor_set(v_reuseFailAlloc_278_, 10, v_canon_266_);
lean_ctor_set(v_reuseFailAlloc_278_, 11, v_instanceOverrides_267_);
lean_ctor_set_uint8(v_reuseFailAlloc_278_, sizeof(void*)*12, v_debug_268_);
v___x_275_ = v_reuseFailAlloc_278_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_276_ = lean_st_ref_put(v_a_243_, v___x_275_);
v___x_277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_277_, 0, v_e_242_);
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
size_t v_x_2355__boxed_313_; lean_object* v_res_314_; 
v_x_2355__boxed_313_ = lean_unbox_usize(v_x_310_);
lean_dec(v_x_310_);
v_res_314_ = l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0(v_00_u03b2_308_, v_x_309_, v_x_2355__boxed_313_, v_x_311_, v_x_312_);
lean_dec_ref(v_x_312_);
lean_dec_ref(v_x_311_);
lean_dec_ref(v_x_309_);
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
lean_dec_ref(v_k_333_);
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
size_t v_x_2379__boxed_349_; size_t v_x_2380__boxed_350_; lean_object* v_res_351_; 
v_x_2379__boxed_349_ = lean_unbox_usize(v_x_345_);
lean_dec(v_x_345_);
v_x_2380__boxed_350_ = lean_unbox_usize(v_x_346_);
lean_dec(v_x_346_);
v_res_351_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2(v_00_u03b2_343_, v_x_344_, v_x_2379__boxed_349_, v_x_2380__boxed_350_, v_x_347_, v_x_348_);
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
v___x_380_ = l_Lean_Meta_Sym_instInhabitedSymM___redArg();
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0(lean_object* v_msg_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_){
_start:
{
lean_object* v___x_389_; lean_object* v___x_698__overap_390_; lean_object* v___x_391_; 
v___x_389_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0, &l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0);
v___x_698__overap_390_ = lean_panic_fn_borrowed(v___x_389_, v_msg_381_);
lean_inc(v___y_387_);
lean_inc_ref(v___y_386_);
lean_inc(v___y_385_);
lean_inc_ref(v___y_384_);
lean_inc(v___y_383_);
lean_inc_ref(v___y_382_);
v___x_391_ = lean_apply_7(v___x_698__overap_390_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, lean_box(0));
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
lean_object* v___x_418_; lean_object* v_share_419_; lean_object* v___x_420_; uint64_t v___x_421_; size_t v___x_422_; lean_object* v___x_423_; size_t v___x_424_; size_t v___x_425_; uint8_t v___x_426_; 
v___x_418_ = lean_st_ref_get(v_a_412_);
v_share_419_ = lean_ctor_get(v___x_418_, 0);
lean_inc_ref(v_share_419_);
lean_dec(v___x_418_);
v___x_420_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy;
v___x_421_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_410_);
v___x_422_ = lean_uint64_to_usize(v___x_421_);
v___x_423_ = l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg(v_share_419_, v___x_422_, v_e_410_, v___x_420_);
lean_dec_ref(v_share_419_);
v___x_424_ = lean_ptr_addr(v___x_423_);
lean_dec_ref(v___x_423_);
v___x_425_ = lean_ptr_addr(v_e_410_);
v___x_426_ = lean_usize_dec_eq(v___x_424_, v___x_425_);
if (v___x_426_ == 0)
{
lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_427_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__3, &l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__3_once, _init_l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__3);
v___x_428_ = l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0(v___x_427_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_);
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
lean_dec_ref(v_e_431_);
return v_res_439_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2(void){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_450_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__1));
v___x_451_ = lean_unsigned_to_nat(16u);
v___x_452_ = lean_unsigned_to_nat(62u);
v___x_453_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__0));
v___x_454_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_455_ = l_mkPanicMessageWithDecl(v___x_454_, v___x_453_, v___x_452_, v___x_451_, v___x_450_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM___redArg(lean_object* v_k_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_){
_start:
{
lean_object* v___x_464_; lean_object* v___x_465_; uint8_t v_debug_466_; lean_object* v___x_467_; lean_object* v_env_468_; lean_object* v___x_469_; lean_object* v___x_470_; uint8_t v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_464_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0, &l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0);
v___x_465_ = lean_st_ref_get(v_a_458_);
v_debug_466_ = lean_ctor_get_uint8(v___x_465_, sizeof(void*)*12);
lean_dec(v___x_465_);
v___x_467_ = lean_st_ref_get(v_a_462_);
v_env_468_ = lean_ctor_get(v___x_467_, 0);
lean_inc_ref(v_env_468_);
lean_dec(v___x_467_);
v___x_469_ = lean_box(v_debug_466_);
v___x_470_ = lean_apply_1(v_k_456_, v___x_469_);
v___x_471_ = 0;
v___x_472_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_472_, 0, v_env_468_);
lean_ctor_set_uint8(v___x_472_, sizeof(void*)*1, v___x_471_);
lean_ctor_set_uint8(v___x_472_, sizeof(void*)*1 + 1, v___x_471_);
v___x_473_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___x_470_, v___x_472_, v_a_458_);
if (lean_obj_tag(v___x_473_) == 0)
{
lean_object* v_a_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_485_; 
v_a_474_ = lean_ctor_get(v___x_473_, 0);
v_isSharedCheck_485_ = !lean_is_exclusive(v___x_473_);
if (v_isSharedCheck_485_ == 0)
{
v___x_476_ = v___x_473_;
v_isShared_477_ = v_isSharedCheck_485_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_a_474_);
lean_dec(v___x_473_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_485_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
if (lean_obj_tag(v_a_474_) == 0)
{
lean_object* v___x_478_; lean_object* v___x_1316__overap_479_; lean_object* v___x_480_; 
lean_dec_ref_known(v_a_474_, 1);
lean_del_object(v___x_476_);
v___x_478_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2, &l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2_once, _init_l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2);
v___x_1316__overap_479_ = l_panic___redArg(v___x_464_, v___x_478_);
lean_inc(v_a_462_);
lean_inc_ref(v_a_461_);
lean_inc(v_a_460_);
lean_inc_ref(v_a_459_);
lean_inc(v_a_458_);
lean_inc_ref(v_a_457_);
v___x_480_ = lean_apply_7(v___x_1316__overap_479_, v_a_457_, v_a_458_, v_a_459_, v_a_460_, v_a_461_, v_a_462_, lean_box(0));
return v___x_480_;
}
else
{
lean_object* v_a_481_; lean_object* v___x_483_; 
v_a_481_ = lean_ctor_get(v_a_474_, 0);
lean_inc(v_a_481_);
lean_dec_ref_known(v_a_474_, 1);
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 0, v_a_481_);
v___x_483_ = v___x_476_;
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
v_a_486_ = lean_ctor_get(v___x_473_, 0);
v_isSharedCheck_493_ = !lean_is_exclusive(v___x_473_);
if (v_isSharedCheck_493_ == 0)
{
v___x_488_ = v___x_473_;
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_a_486_);
lean_dec(v___x_473_);
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
lean_object* v___x_512_; lean_object* v___x_513_; uint8_t v_debug_514_; lean_object* v___x_515_; lean_object* v_env_516_; lean_object* v___x_517_; lean_object* v___x_518_; uint8_t v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_512_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0, &l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0);
v___x_513_ = lean_st_ref_get(v_a_506_);
v_debug_514_ = lean_ctor_get_uint8(v___x_513_, sizeof(void*)*12);
lean_dec(v___x_513_);
v___x_515_ = lean_st_ref_get(v_a_510_);
v_env_516_ = lean_ctor_get(v___x_515_, 0);
lean_inc_ref(v_env_516_);
lean_dec(v___x_515_);
v___x_517_ = lean_box(v_debug_514_);
v___x_518_ = lean_apply_1(v_k_504_, v___x_517_);
v___x_519_ = 0;
v___x_520_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_520_, 0, v_env_516_);
lean_ctor_set_uint8(v___x_520_, sizeof(void*)*1, v___x_519_);
lean_ctor_set_uint8(v___x_520_, sizeof(void*)*1 + 1, v___x_519_);
v___x_521_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___x_518_, v___x_520_, v_a_506_);
if (lean_obj_tag(v___x_521_) == 0)
{
lean_object* v_a_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_533_; 
v_a_522_ = lean_ctor_get(v___x_521_, 0);
v_isSharedCheck_533_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_533_ == 0)
{
v___x_524_ = v___x_521_;
v_isShared_525_ = v_isSharedCheck_533_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_a_522_);
lean_dec(v___x_521_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_533_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
if (lean_obj_tag(v_a_522_) == 0)
{
lean_object* v___x_526_; lean_object* v___x_1339__overap_527_; lean_object* v___x_528_; 
lean_dec_ref_known(v_a_522_, 1);
lean_del_object(v___x_524_);
v___x_526_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2, &l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2_once, _init_l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2);
v___x_1339__overap_527_ = l_panic___redArg(v___x_512_, v___x_526_);
lean_inc(v_a_510_);
lean_inc_ref(v_a_509_);
lean_inc(v_a_508_);
lean_inc_ref(v_a_507_);
lean_inc(v_a_506_);
lean_inc_ref(v_a_505_);
v___x_528_ = lean_apply_7(v___x_1339__overap_527_, v_a_505_, v_a_506_, v_a_507_, v_a_508_, v_a_509_, v_a_510_, lean_box(0));
return v___x_528_;
}
else
{
lean_object* v_a_529_; lean_object* v___x_531_; 
v_a_529_ = lean_ctor_get(v_a_522_, 0);
lean_inc(v_a_529_);
lean_dec_ref_known(v_a_522_, 1);
if (v_isShared_525_ == 0)
{
lean_ctor_set(v___x_524_, 0, v_a_529_);
v___x_531_ = v___x_524_;
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
v_a_534_ = lean_ctor_get(v___x_521_, 0);
v_isSharedCheck_541_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_541_ == 0)
{
v___x_536_ = v___x_521_;
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_a_534_);
lean_dec(v___x_521_);
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
static lean_object* _init_l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__0(void){
_start:
{
lean_object* v___x_576_; 
v___x_576_ = l_Std_HashMap_instInhabited___redArg();
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1(lean_object* v_msg_577_, uint8_t v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_){
_start:
{
lean_object* v___x_581_; lean_object* v___f_582_; lean_object* v___f_583_; lean_object* v___f_584_; lean_object* v___x_534__overap_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_581_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__0, &l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__0);
v___f_582_ = lean_alloc_closure((void*)(l_EStateM_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_582_, 0, v___x_581_);
v___f_583_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_583_, 0, v___f_582_);
v___f_584_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_584_, 0, v___f_583_);
v___x_534__overap_585_ = lean_panic_fn_borrowed(v___f_584_, v_msg_577_);
lean_dec_ref(v___f_584_);
v___x_586_ = lean_box(v___y_578_);
lean_inc_ref(v___y_579_);
v___x_587_ = lean_apply_3(v___x_534__overap_585_, v___x_586_, v___y_579_, v___y_580_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___boxed(lean_object* v_msg_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_){
_start:
{
uint8_t v___y_635__boxed_592_; lean_object* v_res_593_; 
v___y_635__boxed_592_ = lean_unbox(v___y_589_);
v_res_593_ = l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1(v_msg_588_, v___y_635__boxed_592_, v___y_590_, v___y_591_);
lean_dec_ref(v___y_590_);
return v_res_593_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_594_, lean_object* v_i_595_, lean_object* v_k_596_){
_start:
{
lean_object* v___x_597_; uint8_t v___x_598_; 
v___x_597_ = lean_array_get_size(v_keys_594_);
v___x_598_ = lean_nat_dec_lt(v_i_595_, v___x_597_);
if (v___x_598_ == 0)
{
lean_dec(v_i_595_);
return v___x_598_;
}
else
{
lean_object* v_k_x27_599_; uint8_t v___x_600_; 
v_k_x27_599_ = lean_array_fget_borrowed(v_keys_594_, v_i_595_);
v___x_600_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_k_596_, v_k_x27_599_);
if (v___x_600_ == 0)
{
lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_601_ = lean_unsigned_to_nat(1u);
v___x_602_ = lean_nat_add(v_i_595_, v___x_601_);
lean_dec(v_i_595_);
v_i_595_ = v___x_602_;
goto _start;
}
else
{
lean_dec(v_i_595_);
return v___x_598_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_604_, lean_object* v_i_605_, lean_object* v_k_606_){
_start:
{
uint8_t v_res_607_; lean_object* v_r_608_; 
v_res_607_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg(v_keys_604_, v_i_605_, v_k_606_);
lean_dec_ref(v_k_606_);
lean_dec_ref(v_keys_604_);
v_r_608_ = lean_box(v_res_607_);
return v_r_608_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg(lean_object* v_x_609_, size_t v_x_610_, lean_object* v_x_611_){
_start:
{
if (lean_obj_tag(v_x_609_) == 0)
{
lean_object* v_es_612_; lean_object* v___x_613_; size_t v___x_614_; size_t v___x_615_; lean_object* v_j_616_; lean_object* v___x_617_; 
v_es_612_ = lean_ctor_get(v_x_609_, 0);
v___x_613_ = lean_box(2);
v___x_614_ = ((size_t)31ULL);
v___x_615_ = lean_usize_land(v_x_610_, v___x_614_);
v_j_616_ = lean_usize_to_nat(v___x_615_);
v___x_617_ = lean_array_get_borrowed(v___x_613_, v_es_612_, v_j_616_);
lean_dec(v_j_616_);
switch(lean_obj_tag(v___x_617_))
{
case 0:
{
lean_object* v_key_618_; uint8_t v___x_619_; 
v_key_618_ = lean_ctor_get(v___x_617_, 0);
v___x_619_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_611_, v_key_618_);
return v___x_619_;
}
case 1:
{
lean_object* v_node_620_; size_t v___x_621_; size_t v___x_622_; 
v_node_620_ = lean_ctor_get(v___x_617_, 0);
v___x_621_ = ((size_t)5ULL);
v___x_622_ = lean_usize_shift_right(v_x_610_, v___x_621_);
v_x_609_ = v_node_620_;
v_x_610_ = v___x_622_;
goto _start;
}
default: 
{
uint8_t v___x_624_; 
v___x_624_ = 0;
return v___x_624_;
}
}
}
else
{
lean_object* v_ks_625_; lean_object* v___x_626_; uint8_t v___x_627_; 
v_ks_625_ = lean_ctor_get(v_x_609_, 0);
v___x_626_ = lean_unsigned_to_nat(0u);
v___x_627_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg(v_ks_625_, v___x_626_, v_x_611_);
return v___x_627_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg___boxed(lean_object* v_x_628_, lean_object* v_x_629_, lean_object* v_x_630_){
_start:
{
size_t v_x_670__boxed_631_; uint8_t v_res_632_; lean_object* v_r_633_; 
v_x_670__boxed_631_ = lean_unbox_usize(v_x_629_);
lean_dec(v_x_629_);
v_res_632_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg(v_x_628_, v_x_670__boxed_631_, v_x_630_);
lean_dec_ref(v_x_630_);
lean_dec_ref(v_x_628_);
v_r_633_ = lean_box(v_res_632_);
return v_r_633_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg(lean_object* v_x_634_, lean_object* v_x_635_){
_start:
{
uint64_t v___x_636_; size_t v___x_637_; uint8_t v___x_638_; 
v___x_636_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_635_);
v___x_637_ = lean_uint64_to_usize(v___x_636_);
v___x_638_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg(v_x_634_, v___x_637_, v_x_635_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg___boxed(lean_object* v_x_639_, lean_object* v_x_640_){
_start:
{
uint8_t v_res_641_; lean_object* v_r_642_; 
v_res_641_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg(v_x_639_, v_x_640_);
lean_dec_ref(v_x_640_);
lean_dec_ref(v_x_639_);
v_r_642_ = lean_box(v_res_641_);
return v_r_642_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__2(void){
_start:
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_645_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__1));
v___x_646_ = lean_unsigned_to_nat(2u);
v___x_647_ = lean_unsigned_to_nat(74u);
v___x_648_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__0));
v___x_649_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_650_ = l_mkPanicMessageWithDecl(v___x_649_, v___x_648_, v___x_647_, v___x_646_, v___x_645_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_assertShared(lean_object* v_e_651_, uint8_t v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_){
_start:
{
uint8_t v___x_655_; 
v___x_655_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg(v_a_654_, v_e_651_);
if (v___x_655_ == 0)
{
lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_656_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__2, &l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__2_once, _init_l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__2);
v___x_657_ = l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1(v___x_656_, v_a_652_, v_a_653_, v_a_654_);
return v___x_657_;
}
else
{
lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_658_ = lean_box(0);
v___x_659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_659_, 0, v___x_658_);
lean_ctor_set(v___x_659_, 1, v_a_654_);
return v___x_659_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_assertShared___boxed(lean_object* v_e_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_){
_start:
{
uint8_t v_a_boxed_664_; lean_object* v_res_665_; 
v_a_boxed_664_ = lean_unbox(v_a_661_);
v_res_665_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_e_660_, v_a_boxed_664_, v_a_662_, v_a_663_);
lean_dec_ref(v_a_662_);
lean_dec_ref(v_e_660_);
return v_res_665_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0(lean_object* v_00_u03b2_666_, lean_object* v_x_667_, lean_object* v_x_668_){
_start:
{
uint8_t v___x_669_; 
v___x_669_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg(v_x_667_, v_x_668_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___boxed(lean_object* v_00_u03b2_670_, lean_object* v_x_671_, lean_object* v_x_672_){
_start:
{
uint8_t v_res_673_; lean_object* v_r_674_; 
v_res_673_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0(v_00_u03b2_670_, v_x_671_, v_x_672_);
lean_dec_ref(v_x_672_);
lean_dec_ref(v_x_671_);
v_r_674_ = lean_box(v_res_673_);
return v_r_674_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0(lean_object* v_00_u03b2_675_, lean_object* v_x_676_, size_t v_x_677_, lean_object* v_x_678_){
_start:
{
uint8_t v___x_679_; 
v___x_679_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg(v_x_676_, v_x_677_, v_x_678_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___boxed(lean_object* v_00_u03b2_680_, lean_object* v_x_681_, lean_object* v_x_682_, lean_object* v_x_683_){
_start:
{
size_t v_x_769__boxed_684_; uint8_t v_res_685_; lean_object* v_r_686_; 
v_x_769__boxed_684_ = lean_unbox_usize(v_x_682_);
lean_dec(v_x_682_);
v_res_685_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0(v_00_u03b2_680_, v_x_681_, v_x_769__boxed_684_, v_x_683_);
lean_dec_ref(v_x_683_);
lean_dec_ref(v_x_681_);
v_r_686_ = lean_box(v_res_685_);
return v_r_686_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_687_, lean_object* v_keys_688_, lean_object* v_vals_689_, lean_object* v_heq_690_, lean_object* v_i_691_, lean_object* v_k_692_){
_start:
{
uint8_t v___x_693_; 
v___x_693_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg(v_keys_688_, v_i_691_, v_k_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_694_, lean_object* v_keys_695_, lean_object* v_vals_696_, lean_object* v_heq_697_, lean_object* v_i_698_, lean_object* v_k_699_){
_start:
{
uint8_t v_res_700_; lean_object* v_r_701_; 
v_res_700_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2(v_00_u03b2_694_, v_keys_695_, v_vals_696_, v_heq_697_, v_i_698_, v_k_699_);
lean_dec_ref(v_k_699_);
lean_dec_ref(v_vals_696_);
lean_dec_ref(v_keys_695_);
v_r_701_ = lean_box(v_res_700_);
return v_r_701_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__10(void){
_start:
{
lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_721_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__9));
v___x_722_ = l_ReaderT_instMonad___redArg(v___x_721_);
return v___x_722_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__13(void){
_start:
{
lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_725_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__10, &l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__10_once, _init_l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__10);
v___x_726_ = lean_alloc_closure((void*)(l_ReaderT_read___boxed), 4, 3);
lean_closure_set(v___x_726_, 0, lean_box(0));
lean_closure_set(v___x_726_, 1, lean_box(0));
lean_closure_set(v___x_726_, 2, v___x_725_);
return v___x_726_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__14(void){
_start:
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_727_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__13, &l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__13_once, _init_l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__13);
v___x_728_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__12));
v___x_729_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__11));
v___x_730_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_730_, 0, v___x_729_);
lean_ctor_set(v___x_730_, 1, v___x_728_);
lean_ctor_set(v___x_730_, 2, v___x_727_);
return v___x_730_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM(void){
_start:
{
lean_object* v___x_731_; 
v___x_731_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__14, &l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__14_once, _init_l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__14);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLitS___redArg(lean_object* v_inst_732_, lean_object* v_l_733_){
_start:
{
lean_object* v_share1_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
v_share1_734_ = lean_ctor_get(v_inst_732_, 0);
lean_inc(v_share1_734_);
lean_dec_ref(v_inst_732_);
v___x_735_ = l_Lean_Expr_lit___override(v_l_733_);
v___x_736_ = lean_apply_1(v_share1_734_, v___x_735_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLitS(lean_object* v_m_737_, lean_object* v_inst_738_, lean_object* v_l_739_){
_start:
{
lean_object* v___x_740_; 
v___x_740_ = l_Lean_Meta_Sym_Internal_mkLitS___redArg(v_inst_738_, v_l_739_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___redArg(lean_object* v_inst_741_, lean_object* v_declName_742_, lean_object* v_us_743_){
_start:
{
lean_object* v_share1_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
v_share1_744_ = lean_ctor_get(v_inst_741_, 0);
lean_inc(v_share1_744_);
lean_dec_ref(v_inst_741_);
v___x_745_ = l_Lean_Expr_const___override(v_declName_742_, v_us_743_);
v___x_746_ = lean_apply_1(v_share1_744_, v___x_745_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS(lean_object* v_m_747_, lean_object* v_inst_748_, lean_object* v_declName_749_, lean_object* v_us_750_){
_start:
{
lean_object* v___x_751_; 
v___x_751_ = l_Lean_Meta_Sym_Internal_mkConstS___redArg(v_inst_748_, v_declName_749_, v_us_750_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___redArg(lean_object* v_inst_752_, lean_object* v_idx_753_){
_start:
{
lean_object* v_share1_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
v_share1_754_ = lean_ctor_get(v_inst_752_, 0);
lean_inc(v_share1_754_);
lean_dec_ref(v_inst_752_);
v___x_755_ = l_Lean_Expr_bvar___override(v_idx_753_);
v___x_756_ = lean_apply_1(v_share1_754_, v___x_755_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS(lean_object* v_m_757_, lean_object* v_inst_758_, lean_object* v_idx_759_){
_start:
{
lean_object* v___x_760_; 
v___x_760_ = l_Lean_Meta_Sym_Internal_mkBVarS___redArg(v_inst_758_, v_idx_759_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS___redArg(lean_object* v_inst_761_, lean_object* v_u_762_){
_start:
{
lean_object* v_share1_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v_share1_763_ = lean_ctor_get(v_inst_761_, 0);
lean_inc(v_share1_763_);
lean_dec_ref(v_inst_761_);
v___x_764_ = l_Lean_Expr_sort___override(v_u_762_);
v___x_765_ = lean_apply_1(v_share1_763_, v___x_764_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS(lean_object* v_m_766_, lean_object* v_inst_767_, lean_object* v_u_768_){
_start:
{
lean_object* v___x_769_; 
v___x_769_ = l_Lean_Meta_Sym_Internal_mkSortS___redArg(v_inst_767_, v_u_768_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___redArg(lean_object* v_inst_770_, lean_object* v_fvarId_771_){
_start:
{
lean_object* v_share1_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
v_share1_772_ = lean_ctor_get(v_inst_770_, 0);
lean_inc(v_share1_772_);
lean_dec_ref(v_inst_770_);
v___x_773_ = l_Lean_Expr_fvar___override(v_fvarId_771_);
v___x_774_ = lean_apply_1(v_share1_772_, v___x_773_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS(lean_object* v_m_775_, lean_object* v_inst_776_, lean_object* v_fvarId_777_){
_start:
{
lean_object* v___x_778_; 
v___x_778_ = l_Lean_Meta_Sym_Internal_mkFVarS___redArg(v_inst_776_, v_fvarId_777_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMVarS___redArg(lean_object* v_inst_779_, lean_object* v_mvarId_780_){
_start:
{
lean_object* v_share1_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
v_share1_781_ = lean_ctor_get(v_inst_779_, 0);
lean_inc(v_share1_781_);
lean_dec_ref(v_inst_779_);
v___x_782_ = l_Lean_Expr_mvar___override(v_mvarId_780_);
v___x_783_ = lean_apply_1(v_share1_781_, v___x_782_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMVarS(lean_object* v_m_784_, lean_object* v_inst_785_, lean_object* v_mvarId_786_){
_start:
{
lean_object* v___x_787_; 
v___x_787_ = l_Lean_Meta_Sym_Internal_mkMVarS___redArg(v_inst_785_, v_mvarId_786_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__0(lean_object* v_d_788_, lean_object* v_e_789_, lean_object* v_share1_790_, lean_object* v_____r_791_){
_start:
{
lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_792_ = l_Lean_Expr_mdata___override(v_d_788_, v_e_789_);
v___x_793_ = lean_apply_1(v_share1_790_, v___x_792_);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1(lean_object* v___f_794_, lean_object* v_____r_795_){
_start:
{
lean_object* v___x_796_; 
v___x_796_ = lean_apply_1(v___f_794_, v_____r_795_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__2(lean_object* v___f_797_, lean_object* v_assertShared_798_, lean_object* v_e_799_, lean_object* v_toBind_800_, lean_object* v___f_801_, uint8_t v_____do__lift_802_){
_start:
{
if (v_____do__lift_802_ == 0)
{
lean_object* v___x_803_; lean_object* v___x_804_; 
lean_dec(v___f_801_);
lean_dec(v_toBind_800_);
lean_dec_ref(v_e_799_);
lean_dec(v_assertShared_798_);
v___x_803_ = lean_box(0);
v___x_804_ = lean_apply_1(v___f_797_, v___x_803_);
return v___x_804_;
}
else
{
lean_object* v___x_805_; lean_object* v___x_806_; 
lean_dec(v___f_797_);
v___x_805_ = lean_apply_1(v_assertShared_798_, v_e_799_);
v___x_806_ = lean_apply_4(v_toBind_800_, lean_box(0), lean_box(0), v___x_805_, v___f_801_);
return v___x_806_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__2___boxed(lean_object* v___f_807_, lean_object* v_assertShared_808_, lean_object* v_e_809_, lean_object* v_toBind_810_, lean_object* v___f_811_, lean_object* v_____do__lift_812_){
_start:
{
uint8_t v_____do__lift_63__boxed_813_; lean_object* v_res_814_; 
v_____do__lift_63__boxed_813_ = lean_unbox(v_____do__lift_812_);
v_res_814_ = l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__2(v___f_807_, v_assertShared_808_, v_e_809_, v_toBind_810_, v___f_811_, v_____do__lift_63__boxed_813_);
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg(lean_object* v_inst_815_, lean_object* v_inst_816_, lean_object* v_d_817_, lean_object* v_e_818_){
_start:
{
lean_object* v_toBind_819_; lean_object* v_share1_820_; lean_object* v_assertShared_821_; lean_object* v_isDebugEnabled_822_; lean_object* v___f_823_; lean_object* v___f_824_; lean_object* v___f_825_; lean_object* v___x_826_; 
v_toBind_819_ = lean_ctor_get(v_inst_816_, 1);
lean_inc_n(v_toBind_819_, 2);
lean_dec_ref(v_inst_816_);
v_share1_820_ = lean_ctor_get(v_inst_815_, 0);
lean_inc(v_share1_820_);
v_assertShared_821_ = lean_ctor_get(v_inst_815_, 1);
lean_inc(v_assertShared_821_);
v_isDebugEnabled_822_ = lean_ctor_get(v_inst_815_, 2);
lean_inc(v_isDebugEnabled_822_);
lean_dec_ref(v_inst_815_);
lean_inc_ref(v_e_818_);
v___f_823_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__0), 4, 3);
lean_closure_set(v___f_823_, 0, v_d_817_);
lean_closure_set(v___f_823_, 1, v_e_818_);
lean_closure_set(v___f_823_, 2, v_share1_820_);
lean_inc_ref(v___f_823_);
v___f_824_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_824_, 0, v___f_823_);
v___f_825_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_825_, 0, v___f_823_);
lean_closure_set(v___f_825_, 1, v_assertShared_821_);
lean_closure_set(v___f_825_, 2, v_e_818_);
lean_closure_set(v___f_825_, 3, v_toBind_819_);
lean_closure_set(v___f_825_, 4, v___f_824_);
v___x_826_ = lean_apply_4(v_toBind_819_, lean_box(0), lean_box(0), v_isDebugEnabled_822_, v___f_825_);
return v___x_826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS(lean_object* v_m_827_, lean_object* v_inst_828_, lean_object* v_inst_829_, lean_object* v_d_830_, lean_object* v_e_831_){
_start:
{
lean_object* v___x_832_; 
v___x_832_ = l_Lean_Meta_Sym_Internal_mkMDataS___redArg(v_inst_828_, v_inst_829_, v_d_830_, v_e_831_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__0(lean_object* v_structName_833_, lean_object* v_idx_834_, lean_object* v_struct_835_, lean_object* v_share1_836_, lean_object* v_____r_837_){
_start:
{
lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_838_ = l_Lean_Expr_proj___override(v_structName_833_, v_idx_834_, v_struct_835_);
v___x_839_ = lean_apply_1(v_share1_836_, v___x_838_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__2(lean_object* v___f_840_, lean_object* v_assertShared_841_, lean_object* v_struct_842_, lean_object* v_toBind_843_, lean_object* v___f_844_, uint8_t v_____do__lift_845_){
_start:
{
if (v_____do__lift_845_ == 0)
{
lean_object* v___x_846_; lean_object* v___x_847_; 
lean_dec(v___f_844_);
lean_dec(v_toBind_843_);
lean_dec_ref(v_struct_842_);
lean_dec(v_assertShared_841_);
v___x_846_ = lean_box(0);
v___x_847_ = lean_apply_1(v___f_840_, v___x_846_);
return v___x_847_;
}
else
{
lean_object* v___x_848_; lean_object* v___x_849_; 
lean_dec(v___f_840_);
v___x_848_ = lean_apply_1(v_assertShared_841_, v_struct_842_);
v___x_849_ = lean_apply_4(v_toBind_843_, lean_box(0), lean_box(0), v___x_848_, v___f_844_);
return v___x_849_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__2___boxed(lean_object* v___f_850_, lean_object* v_assertShared_851_, lean_object* v_struct_852_, lean_object* v_toBind_853_, lean_object* v___f_854_, lean_object* v_____do__lift_855_){
_start:
{
uint8_t v_____do__lift_57__boxed_856_; lean_object* v_res_857_; 
v_____do__lift_57__boxed_856_ = lean_unbox(v_____do__lift_855_);
v_res_857_ = l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__2(v___f_850_, v_assertShared_851_, v_struct_852_, v_toBind_853_, v___f_854_, v_____do__lift_57__boxed_856_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___redArg(lean_object* v_inst_858_, lean_object* v_inst_859_, lean_object* v_structName_860_, lean_object* v_idx_861_, lean_object* v_struct_862_){
_start:
{
lean_object* v_toBind_863_; lean_object* v_share1_864_; lean_object* v_assertShared_865_; lean_object* v_isDebugEnabled_866_; lean_object* v___f_867_; lean_object* v___f_868_; lean_object* v___f_869_; lean_object* v___x_870_; 
v_toBind_863_ = lean_ctor_get(v_inst_859_, 1);
lean_inc_n(v_toBind_863_, 2);
lean_dec_ref(v_inst_859_);
v_share1_864_ = lean_ctor_get(v_inst_858_, 0);
lean_inc(v_share1_864_);
v_assertShared_865_ = lean_ctor_get(v_inst_858_, 1);
lean_inc(v_assertShared_865_);
v_isDebugEnabled_866_ = lean_ctor_get(v_inst_858_, 2);
lean_inc(v_isDebugEnabled_866_);
lean_dec_ref(v_inst_858_);
lean_inc_ref(v_struct_862_);
v___f_867_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__0), 5, 4);
lean_closure_set(v___f_867_, 0, v_structName_860_);
lean_closure_set(v___f_867_, 1, v_idx_861_);
lean_closure_set(v___f_867_, 2, v_struct_862_);
lean_closure_set(v___f_867_, 3, v_share1_864_);
lean_inc_ref(v___f_867_);
v___f_868_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_868_, 0, v___f_867_);
v___f_869_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_869_, 0, v___f_867_);
lean_closure_set(v___f_869_, 1, v_assertShared_865_);
lean_closure_set(v___f_869_, 2, v_struct_862_);
lean_closure_set(v___f_869_, 3, v_toBind_863_);
lean_closure_set(v___f_869_, 4, v___f_868_);
v___x_870_ = lean_apply_4(v_toBind_863_, lean_box(0), lean_box(0), v_isDebugEnabled_866_, v___f_869_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS(lean_object* v_m_871_, lean_object* v_inst_872_, lean_object* v_inst_873_, lean_object* v_structName_874_, lean_object* v_idx_875_, lean_object* v_struct_876_){
_start:
{
lean_object* v___x_877_; 
v___x_877_ = l_Lean_Meta_Sym_Internal_mkProjS___redArg(v_inst_872_, v_inst_873_, v_structName_874_, v_idx_875_, v_struct_876_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__0(lean_object* v_f_878_, lean_object* v_a_879_, lean_object* v_share1_880_, lean_object* v_____r_881_){
_start:
{
lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_882_ = l_Lean_Expr_app___override(v_f_878_, v_a_879_);
v___x_883_ = lean_apply_1(v_share1_880_, v___x_882_);
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__2(lean_object* v_assertShared_884_, lean_object* v_a_885_, lean_object* v_toBind_886_, lean_object* v___f_887_, lean_object* v_____r_888_){
_start:
{
lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_889_ = lean_apply_1(v_assertShared_884_, v_a_885_);
v___x_890_ = lean_apply_4(v_toBind_886_, lean_box(0), lean_box(0), v___x_889_, v___f_887_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__1(lean_object* v___f_891_, lean_object* v_assertShared_892_, lean_object* v_a_893_, lean_object* v_toBind_894_, lean_object* v___f_895_, lean_object* v_f_896_, uint8_t v_____do__lift_897_){
_start:
{
if (v_____do__lift_897_ == 0)
{
lean_object* v___x_898_; lean_object* v___x_899_; 
lean_dec_ref(v_f_896_);
lean_dec(v___f_895_);
lean_dec(v_toBind_894_);
lean_dec_ref(v_a_893_);
lean_dec(v_assertShared_892_);
v___x_898_ = lean_box(0);
v___x_899_ = lean_apply_1(v___f_891_, v___x_898_);
return v___x_899_;
}
else
{
lean_object* v___f_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
lean_dec(v___f_891_);
lean_inc(v_toBind_894_);
lean_inc(v_assertShared_892_);
v___f_900_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__2), 5, 4);
lean_closure_set(v___f_900_, 0, v_assertShared_892_);
lean_closure_set(v___f_900_, 1, v_a_893_);
lean_closure_set(v___f_900_, 2, v_toBind_894_);
lean_closure_set(v___f_900_, 3, v___f_895_);
v___x_901_ = lean_apply_1(v_assertShared_892_, v_f_896_);
v___x_902_ = lean_apply_4(v_toBind_894_, lean_box(0), lean_box(0), v___x_901_, v___f_900_);
return v___x_902_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__1___boxed(lean_object* v___f_903_, lean_object* v_assertShared_904_, lean_object* v_a_905_, lean_object* v_toBind_906_, lean_object* v___f_907_, lean_object* v_f_908_, lean_object* v_____do__lift_909_){
_start:
{
uint8_t v_____do__lift_74__boxed_910_; lean_object* v_res_911_; 
v_____do__lift_74__boxed_910_ = lean_unbox(v_____do__lift_909_);
v_res_911_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__1(v___f_903_, v_assertShared_904_, v_a_905_, v_toBind_906_, v___f_907_, v_f_908_, v_____do__lift_74__boxed_910_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg(lean_object* v_inst_912_, lean_object* v_inst_913_, lean_object* v_f_914_, lean_object* v_a_915_){
_start:
{
lean_object* v_toBind_916_; lean_object* v_share1_917_; lean_object* v_assertShared_918_; lean_object* v_isDebugEnabled_919_; lean_object* v___f_920_; lean_object* v___f_921_; lean_object* v___f_922_; lean_object* v___x_923_; 
v_toBind_916_ = lean_ctor_get(v_inst_913_, 1);
lean_inc_n(v_toBind_916_, 2);
lean_dec_ref(v_inst_913_);
v_share1_917_ = lean_ctor_get(v_inst_912_, 0);
lean_inc(v_share1_917_);
v_assertShared_918_ = lean_ctor_get(v_inst_912_, 1);
lean_inc(v_assertShared_918_);
v_isDebugEnabled_919_ = lean_ctor_get(v_inst_912_, 2);
lean_inc(v_isDebugEnabled_919_);
lean_dec_ref(v_inst_912_);
lean_inc_ref(v_a_915_);
lean_inc_ref(v_f_914_);
v___f_920_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__0), 4, 3);
lean_closure_set(v___f_920_, 0, v_f_914_);
lean_closure_set(v___f_920_, 1, v_a_915_);
lean_closure_set(v___f_920_, 2, v_share1_917_);
lean_inc_ref(v___f_920_);
v___f_921_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_921_, 0, v___f_920_);
v___f_922_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_922_, 0, v___f_920_);
lean_closure_set(v___f_922_, 1, v_assertShared_918_);
lean_closure_set(v___f_922_, 2, v_a_915_);
lean_closure_set(v___f_922_, 3, v_toBind_916_);
lean_closure_set(v___f_922_, 4, v___f_921_);
lean_closure_set(v___f_922_, 5, v_f_914_);
v___x_923_ = lean_apply_4(v_toBind_916_, lean_box(0), lean_box(0), v_isDebugEnabled_919_, v___f_922_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS(lean_object* v_m_924_, lean_object* v_inst_925_, lean_object* v_inst_926_, lean_object* v_f_927_, lean_object* v_a_928_){
_start:
{
lean_object* v___x_929_; 
v___x_929_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_925_, v_inst_926_, v_f_927_, v_a_928_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__0(lean_object* v_x_930_, lean_object* v_t_931_, lean_object* v_b_932_, uint8_t v_bi_933_, lean_object* v_share1_934_, lean_object* v_____r_935_){
_start:
{
lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_936_ = l_Lean_Expr_lam___override(v_x_930_, v_t_931_, v_b_932_, v_bi_933_);
v___x_937_ = lean_apply_1(v_share1_934_, v___x_936_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__0___boxed(lean_object* v_x_938_, lean_object* v_t_939_, lean_object* v_b_940_, lean_object* v_bi_941_, lean_object* v_share1_942_, lean_object* v_____r_943_){
_start:
{
uint8_t v_bi_boxed_944_; lean_object* v_res_945_; 
v_bi_boxed_944_ = lean_unbox(v_bi_941_);
v_res_945_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__0(v_x_938_, v_t_939_, v_b_940_, v_bi_boxed_944_, v_share1_942_, v_____r_943_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__2(lean_object* v_assertShared_946_, lean_object* v_b_947_, lean_object* v_toBind_948_, lean_object* v___f_949_, lean_object* v_____r_950_){
_start:
{
lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_951_ = lean_apply_1(v_assertShared_946_, v_b_947_);
v___x_952_ = lean_apply_4(v_toBind_948_, lean_box(0), lean_box(0), v___x_951_, v___f_949_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1(lean_object* v___f_953_, lean_object* v_assertShared_954_, lean_object* v_b_955_, lean_object* v_toBind_956_, lean_object* v___f_957_, lean_object* v_t_958_, uint8_t v_____do__lift_959_){
_start:
{
if (v_____do__lift_959_ == 0)
{
lean_object* v___x_960_; lean_object* v___x_961_; 
lean_dec_ref(v_t_958_);
lean_dec(v___f_957_);
lean_dec(v_toBind_956_);
lean_dec_ref(v_b_955_);
lean_dec(v_assertShared_954_);
v___x_960_ = lean_box(0);
v___x_961_ = lean_apply_1(v___f_953_, v___x_960_);
return v___x_961_;
}
else
{
lean_object* v___f_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
lean_dec(v___f_953_);
lean_inc(v_toBind_956_);
lean_inc(v_assertShared_954_);
v___f_962_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__2), 5, 4);
lean_closure_set(v___f_962_, 0, v_assertShared_954_);
lean_closure_set(v___f_962_, 1, v_b_955_);
lean_closure_set(v___f_962_, 2, v_toBind_956_);
lean_closure_set(v___f_962_, 3, v___f_957_);
v___x_963_ = lean_apply_1(v_assertShared_954_, v_t_958_);
v___x_964_ = lean_apply_4(v_toBind_956_, lean_box(0), lean_box(0), v___x_963_, v___f_962_);
return v___x_964_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1___boxed(lean_object* v___f_965_, lean_object* v_assertShared_966_, lean_object* v_b_967_, lean_object* v_toBind_968_, lean_object* v___f_969_, lean_object* v_t_970_, lean_object* v_____do__lift_971_){
_start:
{
uint8_t v_____do__lift_75__boxed_972_; lean_object* v_res_973_; 
v_____do__lift_75__boxed_972_ = lean_unbox(v_____do__lift_971_);
v_res_973_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1(v___f_965_, v_assertShared_966_, v_b_967_, v_toBind_968_, v___f_969_, v_t_970_, v_____do__lift_75__boxed_972_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(lean_object* v_inst_974_, lean_object* v_inst_975_, lean_object* v_x_976_, uint8_t v_bi_977_, lean_object* v_t_978_, lean_object* v_b_979_){
_start:
{
lean_object* v_toBind_980_; lean_object* v_share1_981_; lean_object* v_assertShared_982_; lean_object* v_isDebugEnabled_983_; lean_object* v___x_984_; lean_object* v___f_985_; lean_object* v___f_986_; lean_object* v___f_987_; lean_object* v___x_988_; 
v_toBind_980_ = lean_ctor_get(v_inst_975_, 1);
lean_inc_n(v_toBind_980_, 2);
lean_dec_ref(v_inst_975_);
v_share1_981_ = lean_ctor_get(v_inst_974_, 0);
lean_inc(v_share1_981_);
v_assertShared_982_ = lean_ctor_get(v_inst_974_, 1);
lean_inc(v_assertShared_982_);
v_isDebugEnabled_983_ = lean_ctor_get(v_inst_974_, 2);
lean_inc(v_isDebugEnabled_983_);
lean_dec_ref(v_inst_974_);
v___x_984_ = lean_box(v_bi_977_);
lean_inc_ref(v_b_979_);
lean_inc_ref(v_t_978_);
v___f_985_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_985_, 0, v_x_976_);
lean_closure_set(v___f_985_, 1, v_t_978_);
lean_closure_set(v___f_985_, 2, v_b_979_);
lean_closure_set(v___f_985_, 3, v___x_984_);
lean_closure_set(v___f_985_, 4, v_share1_981_);
lean_inc_ref(v___f_985_);
v___f_986_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_986_, 0, v___f_985_);
v___f_987_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_987_, 0, v___f_985_);
lean_closure_set(v___f_987_, 1, v_assertShared_982_);
lean_closure_set(v___f_987_, 2, v_b_979_);
lean_closure_set(v___f_987_, 3, v_toBind_980_);
lean_closure_set(v___f_987_, 4, v___f_986_);
lean_closure_set(v___f_987_, 5, v_t_978_);
v___x_988_ = lean_apply_4(v_toBind_980_, lean_box(0), lean_box(0), v_isDebugEnabled_983_, v___f_987_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___boxed(lean_object* v_inst_989_, lean_object* v_inst_990_, lean_object* v_x_991_, lean_object* v_bi_992_, lean_object* v_t_993_, lean_object* v_b_994_){
_start:
{
uint8_t v_bi_boxed_995_; lean_object* v_res_996_; 
v_bi_boxed_995_ = lean_unbox(v_bi_992_);
v_res_996_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v_inst_989_, v_inst_990_, v_x_991_, v_bi_boxed_995_, v_t_993_, v_b_994_);
return v_res_996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS(lean_object* v_m_997_, lean_object* v_inst_998_, lean_object* v_inst_999_, lean_object* v_x_1000_, uint8_t v_bi_1001_, lean_object* v_t_1002_, lean_object* v_b_1003_){
_start:
{
lean_object* v___x_1004_; 
v___x_1004_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v_inst_998_, v_inst_999_, v_x_1000_, v_bi_1001_, v_t_1002_, v_b_1003_);
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___boxed(lean_object* v_m_1005_, lean_object* v_inst_1006_, lean_object* v_inst_1007_, lean_object* v_x_1008_, lean_object* v_bi_1009_, lean_object* v_t_1010_, lean_object* v_b_1011_){
_start:
{
uint8_t v_bi_boxed_1012_; lean_object* v_res_1013_; 
v_bi_boxed_1012_ = lean_unbox(v_bi_1009_);
v_res_1013_ = l_Lean_Meta_Sym_Internal_mkLambdaS(v_m_1005_, v_inst_1006_, v_inst_1007_, v_x_1008_, v_bi_boxed_1012_, v_t_1010_, v_b_1011_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___redArg___lam__0(lean_object* v_x_1014_, lean_object* v_t_1015_, lean_object* v_b_1016_, uint8_t v_bi_1017_, lean_object* v_share1_1018_, lean_object* v_____r_1019_){
_start:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; 
v___x_1020_ = l_Lean_Expr_forallE___override(v_x_1014_, v_t_1015_, v_b_1016_, v_bi_1017_);
v___x_1021_ = lean_apply_1(v_share1_1018_, v___x_1020_);
return v___x_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___redArg___lam__0___boxed(lean_object* v_x_1022_, lean_object* v_t_1023_, lean_object* v_b_1024_, lean_object* v_bi_1025_, lean_object* v_share1_1026_, lean_object* v_____r_1027_){
_start:
{
uint8_t v_bi_boxed_1028_; lean_object* v_res_1029_; 
v_bi_boxed_1028_ = lean_unbox(v_bi_1025_);
v_res_1029_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg___lam__0(v_x_1022_, v_t_1023_, v_b_1024_, v_bi_boxed_1028_, v_share1_1026_, v_____r_1027_);
return v_res_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___redArg(lean_object* v_inst_1030_, lean_object* v_inst_1031_, lean_object* v_x_1032_, uint8_t v_bi_1033_, lean_object* v_t_1034_, lean_object* v_b_1035_){
_start:
{
lean_object* v_toBind_1036_; lean_object* v_share1_1037_; lean_object* v_assertShared_1038_; lean_object* v_isDebugEnabled_1039_; lean_object* v___x_1040_; lean_object* v___f_1041_; lean_object* v___f_1042_; lean_object* v___f_1043_; lean_object* v___x_1044_; 
v_toBind_1036_ = lean_ctor_get(v_inst_1031_, 1);
lean_inc_n(v_toBind_1036_, 2);
lean_dec_ref(v_inst_1031_);
v_share1_1037_ = lean_ctor_get(v_inst_1030_, 0);
lean_inc(v_share1_1037_);
v_assertShared_1038_ = lean_ctor_get(v_inst_1030_, 1);
lean_inc(v_assertShared_1038_);
v_isDebugEnabled_1039_ = lean_ctor_get(v_inst_1030_, 2);
lean_inc(v_isDebugEnabled_1039_);
lean_dec_ref(v_inst_1030_);
v___x_1040_ = lean_box(v_bi_1033_);
lean_inc_ref(v_b_1035_);
lean_inc_ref(v_t_1034_);
v___f_1041_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkForallS___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1041_, 0, v_x_1032_);
lean_closure_set(v___f_1041_, 1, v_t_1034_);
lean_closure_set(v___f_1041_, 2, v_b_1035_);
lean_closure_set(v___f_1041_, 3, v___x_1040_);
lean_closure_set(v___f_1041_, 4, v_share1_1037_);
lean_inc_ref(v___f_1041_);
v___f_1042_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1042_, 0, v___f_1041_);
v___f_1043_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_1043_, 0, v___f_1041_);
lean_closure_set(v___f_1043_, 1, v_assertShared_1038_);
lean_closure_set(v___f_1043_, 2, v_b_1035_);
lean_closure_set(v___f_1043_, 3, v_toBind_1036_);
lean_closure_set(v___f_1043_, 4, v___f_1042_);
lean_closure_set(v___f_1043_, 5, v_t_1034_);
v___x_1044_ = lean_apply_4(v_toBind_1036_, lean_box(0), lean_box(0), v_isDebugEnabled_1039_, v___f_1043_);
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___redArg___boxed(lean_object* v_inst_1045_, lean_object* v_inst_1046_, lean_object* v_x_1047_, lean_object* v_bi_1048_, lean_object* v_t_1049_, lean_object* v_b_1050_){
_start:
{
uint8_t v_bi_boxed_1051_; lean_object* v_res_1052_; 
v_bi_boxed_1051_ = lean_unbox(v_bi_1048_);
v_res_1052_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v_inst_1045_, v_inst_1046_, v_x_1047_, v_bi_boxed_1051_, v_t_1049_, v_b_1050_);
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS(lean_object* v_m_1053_, lean_object* v_inst_1054_, lean_object* v_inst_1055_, lean_object* v_x_1056_, uint8_t v_bi_1057_, lean_object* v_t_1058_, lean_object* v_b_1059_){
_start:
{
lean_object* v___x_1060_; 
v___x_1060_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v_inst_1054_, v_inst_1055_, v_x_1056_, v_bi_1057_, v_t_1058_, v_b_1059_);
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___boxed(lean_object* v_m_1061_, lean_object* v_inst_1062_, lean_object* v_inst_1063_, lean_object* v_x_1064_, lean_object* v_bi_1065_, lean_object* v_t_1066_, lean_object* v_b_1067_){
_start:
{
uint8_t v_bi_boxed_1068_; lean_object* v_res_1069_; 
v_bi_boxed_1068_ = lean_unbox(v_bi_1065_);
v_res_1069_ = l_Lean_Meta_Sym_Internal_mkForallS(v_m_1061_, v_inst_1062_, v_inst_1063_, v_x_1064_, v_bi_boxed_1068_, v_t_1066_, v_b_1067_);
return v_res_1069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__0(lean_object* v_x_1070_, lean_object* v_t_1071_, lean_object* v_v_1072_, lean_object* v_b_1073_, uint8_t v_nondep_1074_, lean_object* v_share1_1075_, lean_object* v_____r_1076_){
_start:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1077_ = l_Lean_Expr_letE___override(v_x_1070_, v_t_1071_, v_v_1072_, v_b_1073_, v_nondep_1074_);
v___x_1078_ = lean_apply_1(v_share1_1075_, v___x_1077_);
return v___x_1078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__0___boxed(lean_object* v_x_1079_, lean_object* v_t_1080_, lean_object* v_v_1081_, lean_object* v_b_1082_, lean_object* v_nondep_1083_, lean_object* v_share1_1084_, lean_object* v_____r_1085_){
_start:
{
uint8_t v_nondep_boxed_1086_; lean_object* v_res_1087_; 
v_nondep_boxed_1086_ = lean_unbox(v_nondep_1083_);
v_res_1087_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__0(v_x_1079_, v_t_1080_, v_v_1081_, v_b_1082_, v_nondep_boxed_1086_, v_share1_1084_, v_____r_1085_);
return v_res_1087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__3(lean_object* v_assertShared_1088_, lean_object* v_v_1089_, lean_object* v_toBind_1090_, lean_object* v___f_1091_, lean_object* v_____r_1092_){
_start:
{
lean_object* v___x_1093_; lean_object* v___x_1094_; 
v___x_1093_ = lean_apply_1(v_assertShared_1088_, v_v_1089_);
v___x_1094_ = lean_apply_4(v_toBind_1090_, lean_box(0), lean_box(0), v___x_1093_, v___f_1091_);
return v___x_1094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1(lean_object* v___f_1095_, lean_object* v_assertShared_1096_, lean_object* v_b_1097_, lean_object* v_toBind_1098_, lean_object* v___f_1099_, lean_object* v_v_1100_, lean_object* v_t_1101_, uint8_t v_____do__lift_1102_){
_start:
{
if (v_____do__lift_1102_ == 0)
{
lean_object* v___x_1103_; lean_object* v___x_1104_; 
lean_dec_ref(v_t_1101_);
lean_dec_ref(v_v_1100_);
lean_dec(v___f_1099_);
lean_dec(v_toBind_1098_);
lean_dec_ref(v_b_1097_);
lean_dec(v_assertShared_1096_);
v___x_1103_ = lean_box(0);
v___x_1104_ = lean_apply_1(v___f_1095_, v___x_1103_);
return v___x_1104_;
}
else
{
lean_object* v___f_1105_; lean_object* v___f_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; 
lean_dec(v___f_1095_);
lean_inc_n(v_toBind_1098_, 2);
lean_inc_n(v_assertShared_1096_, 2);
v___f_1105_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__2), 5, 4);
lean_closure_set(v___f_1105_, 0, v_assertShared_1096_);
lean_closure_set(v___f_1105_, 1, v_b_1097_);
lean_closure_set(v___f_1105_, 2, v_toBind_1098_);
lean_closure_set(v___f_1105_, 3, v___f_1099_);
v___f_1106_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__3), 5, 4);
lean_closure_set(v___f_1106_, 0, v_assertShared_1096_);
lean_closure_set(v___f_1106_, 1, v_v_1100_);
lean_closure_set(v___f_1106_, 2, v_toBind_1098_);
lean_closure_set(v___f_1106_, 3, v___f_1105_);
v___x_1107_ = lean_apply_1(v_assertShared_1096_, v_t_1101_);
v___x_1108_ = lean_apply_4(v_toBind_1098_, lean_box(0), lean_box(0), v___x_1107_, v___f_1106_);
return v___x_1108_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1___boxed(lean_object* v___f_1109_, lean_object* v_assertShared_1110_, lean_object* v_b_1111_, lean_object* v_toBind_1112_, lean_object* v___f_1113_, lean_object* v_v_1114_, lean_object* v_t_1115_, lean_object* v_____do__lift_1116_){
_start:
{
uint8_t v_____do__lift_84__boxed_1117_; lean_object* v_res_1118_; 
v_____do__lift_84__boxed_1117_ = lean_unbox(v_____do__lift_1116_);
v_res_1118_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1(v___f_1109_, v_assertShared_1110_, v_b_1111_, v_toBind_1112_, v___f_1113_, v_v_1114_, v_t_1115_, v_____do__lift_84__boxed_1117_);
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg(lean_object* v_inst_1119_, lean_object* v_inst_1120_, lean_object* v_x_1121_, lean_object* v_t_1122_, lean_object* v_v_1123_, lean_object* v_b_1124_, uint8_t v_nondep_1125_){
_start:
{
lean_object* v_toBind_1126_; lean_object* v_share1_1127_; lean_object* v_assertShared_1128_; lean_object* v_isDebugEnabled_1129_; lean_object* v___x_1130_; lean_object* v___f_1131_; lean_object* v___f_1132_; lean_object* v___f_1133_; lean_object* v___x_1134_; 
v_toBind_1126_ = lean_ctor_get(v_inst_1120_, 1);
lean_inc_n(v_toBind_1126_, 2);
lean_dec_ref(v_inst_1120_);
v_share1_1127_ = lean_ctor_get(v_inst_1119_, 0);
lean_inc(v_share1_1127_);
v_assertShared_1128_ = lean_ctor_get(v_inst_1119_, 1);
lean_inc(v_assertShared_1128_);
v_isDebugEnabled_1129_ = lean_ctor_get(v_inst_1119_, 2);
lean_inc(v_isDebugEnabled_1129_);
lean_dec_ref(v_inst_1119_);
v___x_1130_ = lean_box(v_nondep_1125_);
lean_inc_ref(v_b_1124_);
lean_inc_ref(v_v_1123_);
lean_inc_ref(v_t_1122_);
v___f_1131_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_1131_, 0, v_x_1121_);
lean_closure_set(v___f_1131_, 1, v_t_1122_);
lean_closure_set(v___f_1131_, 2, v_v_1123_);
lean_closure_set(v___f_1131_, 3, v_b_1124_);
lean_closure_set(v___f_1131_, 4, v___x_1130_);
lean_closure_set(v___f_1131_, 5, v_share1_1127_);
lean_inc_ref(v___f_1131_);
v___f_1132_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1132_, 0, v___f_1131_);
v___f_1133_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_1133_, 0, v___f_1131_);
lean_closure_set(v___f_1133_, 1, v_assertShared_1128_);
lean_closure_set(v___f_1133_, 2, v_b_1124_);
lean_closure_set(v___f_1133_, 3, v_toBind_1126_);
lean_closure_set(v___f_1133_, 4, v___f_1132_);
lean_closure_set(v___f_1133_, 5, v_v_1123_);
lean_closure_set(v___f_1133_, 6, v_t_1122_);
v___x_1134_ = lean_apply_4(v_toBind_1126_, lean_box(0), lean_box(0), v_isDebugEnabled_1129_, v___f_1133_);
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___boxed(lean_object* v_inst_1135_, lean_object* v_inst_1136_, lean_object* v_x_1137_, lean_object* v_t_1138_, lean_object* v_v_1139_, lean_object* v_b_1140_, lean_object* v_nondep_1141_){
_start:
{
uint8_t v_nondep_boxed_1142_; lean_object* v_res_1143_; 
v_nondep_boxed_1142_ = lean_unbox(v_nondep_1141_);
v_res_1143_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1135_, v_inst_1136_, v_x_1137_, v_t_1138_, v_v_1139_, v_b_1140_, v_nondep_boxed_1142_);
return v_res_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS(lean_object* v_m_1144_, lean_object* v_inst_1145_, lean_object* v_inst_1146_, lean_object* v_x_1147_, lean_object* v_t_1148_, lean_object* v_v_1149_, lean_object* v_b_1150_, uint8_t v_nondep_1151_){
_start:
{
lean_object* v___x_1152_; 
v___x_1152_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1145_, v_inst_1146_, v_x_1147_, v_t_1148_, v_v_1149_, v_b_1150_, v_nondep_1151_);
return v___x_1152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___boxed(lean_object* v_m_1153_, lean_object* v_inst_1154_, lean_object* v_inst_1155_, lean_object* v_x_1156_, lean_object* v_t_1157_, lean_object* v_v_1158_, lean_object* v_b_1159_, lean_object* v_nondep_1160_){
_start:
{
uint8_t v_nondep_boxed_1161_; lean_object* v_res_1162_; 
v_nondep_boxed_1161_ = lean_unbox(v_nondep_1160_);
v_res_1162_ = l_Lean_Meta_Sym_Internal_mkLetS(v_m_1153_, v_inst_1154_, v_inst_1155_, v_x_1156_, v_t_1157_, v_v_1158_, v_b_1159_, v_nondep_boxed_1161_);
return v_res_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkHaveS___redArg___lam__0(lean_object* v_x_1163_, lean_object* v_t_1164_, lean_object* v_v_1165_, lean_object* v_b_1166_, lean_object* v_share1_1167_, lean_object* v_____r_1168_){
_start:
{
uint8_t v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; 
v___x_1169_ = 1;
v___x_1170_ = l_Lean_Expr_letE___override(v_x_1163_, v_t_1164_, v_v_1165_, v_b_1166_, v___x_1169_);
v___x_1171_ = lean_apply_1(v_share1_1167_, v___x_1170_);
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkHaveS___redArg(lean_object* v_inst_1172_, lean_object* v_inst_1173_, lean_object* v_x_1174_, lean_object* v_t_1175_, lean_object* v_v_1176_, lean_object* v_b_1177_){
_start:
{
lean_object* v_toBind_1178_; lean_object* v_share1_1179_; lean_object* v_assertShared_1180_; lean_object* v_isDebugEnabled_1181_; lean_object* v___f_1182_; lean_object* v___f_1183_; lean_object* v___f_1184_; lean_object* v___x_1185_; 
v_toBind_1178_ = lean_ctor_get(v_inst_1173_, 1);
lean_inc_n(v_toBind_1178_, 2);
lean_dec_ref(v_inst_1173_);
v_share1_1179_ = lean_ctor_get(v_inst_1172_, 0);
lean_inc(v_share1_1179_);
v_assertShared_1180_ = lean_ctor_get(v_inst_1172_, 1);
lean_inc(v_assertShared_1180_);
v_isDebugEnabled_1181_ = lean_ctor_get(v_inst_1172_, 2);
lean_inc(v_isDebugEnabled_1181_);
lean_dec_ref(v_inst_1172_);
lean_inc_ref(v_b_1177_);
lean_inc_ref(v_v_1176_);
lean_inc_ref(v_t_1175_);
v___f_1182_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkHaveS___redArg___lam__0), 6, 5);
lean_closure_set(v___f_1182_, 0, v_x_1174_);
lean_closure_set(v___f_1182_, 1, v_t_1175_);
lean_closure_set(v___f_1182_, 2, v_v_1176_);
lean_closure_set(v___f_1182_, 3, v_b_1177_);
lean_closure_set(v___f_1182_, 4, v_share1_1179_);
lean_inc_ref(v___f_1182_);
v___f_1183_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1183_, 0, v___f_1182_);
v___f_1184_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_1184_, 0, v___f_1182_);
lean_closure_set(v___f_1184_, 1, v_assertShared_1180_);
lean_closure_set(v___f_1184_, 2, v_b_1177_);
lean_closure_set(v___f_1184_, 3, v_toBind_1178_);
lean_closure_set(v___f_1184_, 4, v___f_1183_);
lean_closure_set(v___f_1184_, 5, v_v_1176_);
lean_closure_set(v___f_1184_, 6, v_t_1175_);
v___x_1185_ = lean_apply_4(v_toBind_1178_, lean_box(0), lean_box(0), v_isDebugEnabled_1181_, v___f_1184_);
return v___x_1185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkHaveS(lean_object* v_m_1186_, lean_object* v_inst_1187_, lean_object* v_inst_1188_, lean_object* v_x_1189_, lean_object* v_t_1190_, lean_object* v_v_1191_, lean_object* v_b_1192_){
_start:
{
lean_object* v___x_1193_; 
v___x_1193_ = l_Lean_Meta_Sym_Internal_mkHaveS___redArg(v_inst_1187_, v_inst_1188_, v_x_1189_, v_t_1190_, v_v_1191_, v_b_1192_);
return v___x_1193_;
}
}
static lean_object* _init_l_Lean_Expr_updateAppS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1196_ = ((lean_object*)(l_Lean_Expr_updateAppS_x21___redArg___closed__1));
v___x_1197_ = lean_unsigned_to_nat(25u);
v___x_1198_ = lean_unsigned_to_nat(148u);
v___x_1199_ = ((lean_object*)(l_Lean_Expr_updateAppS_x21___redArg___closed__0));
v___x_1200_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1201_ = l_mkPanicMessageWithDecl(v___x_1200_, v___x_1199_, v___x_1198_, v___x_1197_, v___x_1196_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateAppS_x21___redArg(lean_object* v_inst_1202_, lean_object* v_inst_1203_, lean_object* v_e_1204_, lean_object* v_newFn_1205_, lean_object* v_newArg_1206_){
_start:
{
if (lean_obj_tag(v_e_1204_) == 5)
{
lean_object* v_toApplicative_1207_; lean_object* v_toPure_1208_; lean_object* v_fn_1209_; lean_object* v_arg_1210_; size_t v___x_1211_; size_t v___x_1212_; uint8_t v___x_1213_; 
v_toApplicative_1207_ = lean_ctor_get(v_inst_1203_, 0);
v_toPure_1208_ = lean_ctor_get(v_toApplicative_1207_, 1);
v_fn_1209_ = lean_ctor_get(v_e_1204_, 0);
v_arg_1210_ = lean_ctor_get(v_e_1204_, 1);
v___x_1211_ = lean_ptr_addr(v_fn_1209_);
v___x_1212_ = lean_ptr_addr(v_newFn_1205_);
v___x_1213_ = lean_usize_dec_eq(v___x_1211_, v___x_1212_);
if (v___x_1213_ == 0)
{
lean_object* v___x_1214_; 
lean_dec_ref_known(v_e_1204_, 2);
v___x_1214_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1202_, v_inst_1203_, v_newFn_1205_, v_newArg_1206_);
return v___x_1214_;
}
else
{
size_t v___x_1215_; size_t v___x_1216_; uint8_t v___x_1217_; 
v___x_1215_ = lean_ptr_addr(v_arg_1210_);
v___x_1216_ = lean_ptr_addr(v_newArg_1206_);
v___x_1217_ = lean_usize_dec_eq(v___x_1215_, v___x_1216_);
if (v___x_1217_ == 0)
{
lean_object* v___x_1218_; 
lean_dec_ref_known(v_e_1204_, 2);
v___x_1218_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1202_, v_inst_1203_, v_newFn_1205_, v_newArg_1206_);
return v___x_1218_;
}
else
{
lean_object* v___x_1219_; 
lean_inc(v_toPure_1208_);
lean_dec_ref(v_newArg_1206_);
lean_dec_ref(v_newFn_1205_);
lean_dec_ref(v_inst_1203_);
lean_dec_ref(v_inst_1202_);
v___x_1219_ = lean_apply_2(v_toPure_1208_, lean_box(0), v_e_1204_);
return v___x_1219_;
}
}
}
else
{
lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; 
lean_dec_ref(v_newArg_1206_);
lean_dec_ref(v_newFn_1205_);
lean_dec_ref(v_e_1204_);
lean_dec_ref(v_inst_1202_);
v___x_1220_ = l_Lean_instInhabitedExpr;
v___x_1221_ = l_instInhabitedOfMonad___redArg(v_inst_1203_, v___x_1220_);
v___x_1222_ = lean_obj_once(&l_Lean_Expr_updateAppS_x21___redArg___closed__2, &l_Lean_Expr_updateAppS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateAppS_x21___redArg___closed__2);
v___x_1223_ = l_panic___redArg(v___x_1221_, v___x_1222_);
lean_dec(v___x_1221_);
return v___x_1223_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateAppS_x21(lean_object* v_m_1224_, lean_object* v_inst_1225_, lean_object* v_inst_1226_, lean_object* v_e_1227_, lean_object* v_newFn_1228_, lean_object* v_newArg_1229_){
_start:
{
if (lean_obj_tag(v_e_1227_) == 5)
{
lean_object* v_toApplicative_1230_; lean_object* v_toPure_1231_; lean_object* v_fn_1232_; lean_object* v_arg_1233_; size_t v___x_1234_; size_t v___x_1235_; uint8_t v___x_1236_; 
v_toApplicative_1230_ = lean_ctor_get(v_inst_1226_, 0);
v_toPure_1231_ = lean_ctor_get(v_toApplicative_1230_, 1);
v_fn_1232_ = lean_ctor_get(v_e_1227_, 0);
v_arg_1233_ = lean_ctor_get(v_e_1227_, 1);
v___x_1234_ = lean_ptr_addr(v_fn_1232_);
v___x_1235_ = lean_ptr_addr(v_newFn_1228_);
v___x_1236_ = lean_usize_dec_eq(v___x_1234_, v___x_1235_);
if (v___x_1236_ == 0)
{
lean_object* v___x_1237_; 
lean_dec_ref_known(v_e_1227_, 2);
v___x_1237_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1225_, v_inst_1226_, v_newFn_1228_, v_newArg_1229_);
return v___x_1237_;
}
else
{
size_t v___x_1238_; size_t v___x_1239_; uint8_t v___x_1240_; 
v___x_1238_ = lean_ptr_addr(v_arg_1233_);
v___x_1239_ = lean_ptr_addr(v_newArg_1229_);
v___x_1240_ = lean_usize_dec_eq(v___x_1238_, v___x_1239_);
if (v___x_1240_ == 0)
{
lean_object* v___x_1241_; 
lean_dec_ref_known(v_e_1227_, 2);
v___x_1241_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1225_, v_inst_1226_, v_newFn_1228_, v_newArg_1229_);
return v___x_1241_;
}
else
{
lean_object* v___x_1242_; 
lean_inc(v_toPure_1231_);
lean_dec_ref(v_newArg_1229_);
lean_dec_ref(v_newFn_1228_);
lean_dec_ref(v_inst_1226_);
lean_dec_ref(v_inst_1225_);
v___x_1242_ = lean_apply_2(v_toPure_1231_, lean_box(0), v_e_1227_);
return v___x_1242_;
}
}
}
else
{
lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
lean_dec_ref(v_newArg_1229_);
lean_dec_ref(v_newFn_1228_);
lean_dec_ref(v_e_1227_);
lean_dec_ref(v_inst_1225_);
v___x_1243_ = l_Lean_instInhabitedExpr;
v___x_1244_ = l_instInhabitedOfMonad___redArg(v_inst_1226_, v___x_1243_);
v___x_1245_ = lean_obj_once(&l_Lean_Expr_updateAppS_x21___redArg___closed__2, &l_Lean_Expr_updateAppS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateAppS_x21___redArg___closed__2);
v___x_1246_ = l_panic___redArg(v___x_1244_, v___x_1245_);
lean_dec(v___x_1244_);
return v___x_1246_;
}
}
}
static lean_object* _init_l_Lean_Expr_updateMDataS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___x_1249_ = ((lean_object*)(l_Lean_Expr_updateMDataS_x21___redArg___closed__1));
v___x_1250_ = lean_unsigned_to_nat(24u);
v___x_1251_ = lean_unsigned_to_nat(152u);
v___x_1252_ = ((lean_object*)(l_Lean_Expr_updateMDataS_x21___redArg___closed__0));
v___x_1253_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1254_ = l_mkPanicMessageWithDecl(v___x_1253_, v___x_1252_, v___x_1251_, v___x_1250_, v___x_1249_);
return v___x_1254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateMDataS_x21___redArg(lean_object* v_inst_1255_, lean_object* v_inst_1256_, lean_object* v_e_1257_, lean_object* v_newExpr_1258_){
_start:
{
if (lean_obj_tag(v_e_1257_) == 10)
{
lean_object* v_toApplicative_1259_; lean_object* v_toPure_1260_; lean_object* v_data_1261_; lean_object* v_expr_1262_; size_t v___x_1263_; size_t v___x_1264_; uint8_t v___x_1265_; 
v_toApplicative_1259_ = lean_ctor_get(v_inst_1256_, 0);
v_toPure_1260_ = lean_ctor_get(v_toApplicative_1259_, 1);
v_data_1261_ = lean_ctor_get(v_e_1257_, 0);
v_expr_1262_ = lean_ctor_get(v_e_1257_, 1);
v___x_1263_ = lean_ptr_addr(v_expr_1262_);
v___x_1264_ = lean_ptr_addr(v_newExpr_1258_);
v___x_1265_ = lean_usize_dec_eq(v___x_1263_, v___x_1264_);
if (v___x_1265_ == 0)
{
lean_object* v___x_1266_; 
lean_inc(v_data_1261_);
lean_dec_ref_known(v_e_1257_, 2);
v___x_1266_ = l_Lean_Meta_Sym_Internal_mkMDataS___redArg(v_inst_1255_, v_inst_1256_, v_data_1261_, v_newExpr_1258_);
return v___x_1266_;
}
else
{
lean_object* v___x_1267_; 
lean_inc(v_toPure_1260_);
lean_dec_ref(v_newExpr_1258_);
lean_dec_ref(v_inst_1256_);
lean_dec_ref(v_inst_1255_);
v___x_1267_ = lean_apply_2(v_toPure_1260_, lean_box(0), v_e_1257_);
return v___x_1267_;
}
}
else
{
lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; 
lean_dec_ref(v_newExpr_1258_);
lean_dec_ref(v_e_1257_);
lean_dec_ref(v_inst_1255_);
v___x_1268_ = l_Lean_instInhabitedExpr;
v___x_1269_ = l_instInhabitedOfMonad___redArg(v_inst_1256_, v___x_1268_);
v___x_1270_ = lean_obj_once(&l_Lean_Expr_updateMDataS_x21___redArg___closed__2, &l_Lean_Expr_updateMDataS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateMDataS_x21___redArg___closed__2);
v___x_1271_ = l_panic___redArg(v___x_1269_, v___x_1270_);
lean_dec(v___x_1269_);
return v___x_1271_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateMDataS_x21(lean_object* v_m_1272_, lean_object* v_inst_1273_, lean_object* v_inst_1274_, lean_object* v_e_1275_, lean_object* v_newExpr_1276_){
_start:
{
if (lean_obj_tag(v_e_1275_) == 10)
{
lean_object* v_toApplicative_1277_; lean_object* v_toPure_1278_; lean_object* v_data_1279_; lean_object* v_expr_1280_; size_t v___x_1281_; size_t v___x_1282_; uint8_t v___x_1283_; 
v_toApplicative_1277_ = lean_ctor_get(v_inst_1274_, 0);
v_toPure_1278_ = lean_ctor_get(v_toApplicative_1277_, 1);
v_data_1279_ = lean_ctor_get(v_e_1275_, 0);
v_expr_1280_ = lean_ctor_get(v_e_1275_, 1);
v___x_1281_ = lean_ptr_addr(v_expr_1280_);
v___x_1282_ = lean_ptr_addr(v_newExpr_1276_);
v___x_1283_ = lean_usize_dec_eq(v___x_1281_, v___x_1282_);
if (v___x_1283_ == 0)
{
lean_object* v___x_1284_; 
lean_inc(v_data_1279_);
lean_dec_ref_known(v_e_1275_, 2);
v___x_1284_ = l_Lean_Meta_Sym_Internal_mkMDataS___redArg(v_inst_1273_, v_inst_1274_, v_data_1279_, v_newExpr_1276_);
return v___x_1284_;
}
else
{
lean_object* v___x_1285_; 
lean_inc(v_toPure_1278_);
lean_dec_ref(v_newExpr_1276_);
lean_dec_ref(v_inst_1274_);
lean_dec_ref(v_inst_1273_);
v___x_1285_ = lean_apply_2(v_toPure_1278_, lean_box(0), v_e_1275_);
return v___x_1285_;
}
}
else
{
lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; 
lean_dec_ref(v_newExpr_1276_);
lean_dec_ref(v_e_1275_);
lean_dec_ref(v_inst_1273_);
v___x_1286_ = l_Lean_instInhabitedExpr;
v___x_1287_ = l_instInhabitedOfMonad___redArg(v_inst_1274_, v___x_1286_);
v___x_1288_ = lean_obj_once(&l_Lean_Expr_updateMDataS_x21___redArg___closed__2, &l_Lean_Expr_updateMDataS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateMDataS_x21___redArg___closed__2);
v___x_1289_ = l_panic___redArg(v___x_1287_, v___x_1288_);
lean_dec(v___x_1287_);
return v___x_1289_;
}
}
}
static lean_object* _init_l_Lean_Expr_updateProjS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; 
v___x_1292_ = ((lean_object*)(l_Lean_Expr_updateProjS_x21___redArg___closed__1));
v___x_1293_ = lean_unsigned_to_nat(25u);
v___x_1294_ = lean_unsigned_to_nat(156u);
v___x_1295_ = ((lean_object*)(l_Lean_Expr_updateProjS_x21___redArg___closed__0));
v___x_1296_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1297_ = l_mkPanicMessageWithDecl(v___x_1296_, v___x_1295_, v___x_1294_, v___x_1293_, v___x_1292_);
return v___x_1297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateProjS_x21___redArg(lean_object* v_inst_1298_, lean_object* v_inst_1299_, lean_object* v_e_1300_, lean_object* v_newExpr_1301_){
_start:
{
if (lean_obj_tag(v_e_1300_) == 11)
{
lean_object* v_toApplicative_1302_; lean_object* v_toPure_1303_; lean_object* v_typeName_1304_; lean_object* v_idx_1305_; lean_object* v_struct_1306_; size_t v___x_1307_; size_t v___x_1308_; uint8_t v___x_1309_; 
v_toApplicative_1302_ = lean_ctor_get(v_inst_1299_, 0);
v_toPure_1303_ = lean_ctor_get(v_toApplicative_1302_, 1);
v_typeName_1304_ = lean_ctor_get(v_e_1300_, 0);
v_idx_1305_ = lean_ctor_get(v_e_1300_, 1);
v_struct_1306_ = lean_ctor_get(v_e_1300_, 2);
v___x_1307_ = lean_ptr_addr(v_struct_1306_);
v___x_1308_ = lean_ptr_addr(v_newExpr_1301_);
v___x_1309_ = lean_usize_dec_eq(v___x_1307_, v___x_1308_);
if (v___x_1309_ == 0)
{
lean_object* v___x_1310_; 
lean_inc(v_idx_1305_);
lean_inc(v_typeName_1304_);
lean_dec_ref_known(v_e_1300_, 3);
v___x_1310_ = l_Lean_Meta_Sym_Internal_mkProjS___redArg(v_inst_1298_, v_inst_1299_, v_typeName_1304_, v_idx_1305_, v_newExpr_1301_);
return v___x_1310_;
}
else
{
lean_object* v___x_1311_; 
lean_inc(v_toPure_1303_);
lean_dec_ref(v_newExpr_1301_);
lean_dec_ref(v_inst_1299_);
lean_dec_ref(v_inst_1298_);
v___x_1311_ = lean_apply_2(v_toPure_1303_, lean_box(0), v_e_1300_);
return v___x_1311_;
}
}
else
{
lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; 
lean_dec_ref(v_newExpr_1301_);
lean_dec_ref(v_e_1300_);
lean_dec_ref(v_inst_1298_);
v___x_1312_ = l_Lean_instInhabitedExpr;
v___x_1313_ = l_instInhabitedOfMonad___redArg(v_inst_1299_, v___x_1312_);
v___x_1314_ = lean_obj_once(&l_Lean_Expr_updateProjS_x21___redArg___closed__2, &l_Lean_Expr_updateProjS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateProjS_x21___redArg___closed__2);
v___x_1315_ = l_panic___redArg(v___x_1313_, v___x_1314_);
lean_dec(v___x_1313_);
return v___x_1315_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateProjS_x21(lean_object* v_m_1316_, lean_object* v_inst_1317_, lean_object* v_inst_1318_, lean_object* v_e_1319_, lean_object* v_newExpr_1320_){
_start:
{
if (lean_obj_tag(v_e_1319_) == 11)
{
lean_object* v_toApplicative_1321_; lean_object* v_toPure_1322_; lean_object* v_typeName_1323_; lean_object* v_idx_1324_; lean_object* v_struct_1325_; size_t v___x_1326_; size_t v___x_1327_; uint8_t v___x_1328_; 
v_toApplicative_1321_ = lean_ctor_get(v_inst_1318_, 0);
v_toPure_1322_ = lean_ctor_get(v_toApplicative_1321_, 1);
v_typeName_1323_ = lean_ctor_get(v_e_1319_, 0);
v_idx_1324_ = lean_ctor_get(v_e_1319_, 1);
v_struct_1325_ = lean_ctor_get(v_e_1319_, 2);
v___x_1326_ = lean_ptr_addr(v_struct_1325_);
v___x_1327_ = lean_ptr_addr(v_newExpr_1320_);
v___x_1328_ = lean_usize_dec_eq(v___x_1326_, v___x_1327_);
if (v___x_1328_ == 0)
{
lean_object* v___x_1329_; 
lean_inc(v_idx_1324_);
lean_inc(v_typeName_1323_);
lean_dec_ref_known(v_e_1319_, 3);
v___x_1329_ = l_Lean_Meta_Sym_Internal_mkProjS___redArg(v_inst_1317_, v_inst_1318_, v_typeName_1323_, v_idx_1324_, v_newExpr_1320_);
return v___x_1329_;
}
else
{
lean_object* v___x_1330_; 
lean_inc(v_toPure_1322_);
lean_dec_ref(v_newExpr_1320_);
lean_dec_ref(v_inst_1318_);
lean_dec_ref(v_inst_1317_);
v___x_1330_ = lean_apply_2(v_toPure_1322_, lean_box(0), v_e_1319_);
return v___x_1330_;
}
}
else
{
lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; 
lean_dec_ref(v_newExpr_1320_);
lean_dec_ref(v_e_1319_);
lean_dec_ref(v_inst_1317_);
v___x_1331_ = l_Lean_instInhabitedExpr;
v___x_1332_ = l_instInhabitedOfMonad___redArg(v_inst_1318_, v___x_1331_);
v___x_1333_ = lean_obj_once(&l_Lean_Expr_updateProjS_x21___redArg___closed__2, &l_Lean_Expr_updateProjS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateProjS_x21___redArg___closed__2);
v___x_1334_ = l_panic___redArg(v___x_1332_, v___x_1333_);
lean_dec(v___x_1332_);
return v___x_1334_;
}
}
}
static lean_object* _init_l_Lean_Expr_updateForallS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; 
v___x_1337_ = ((lean_object*)(l_Lean_Expr_updateForallS_x21___redArg___closed__1));
v___x_1338_ = lean_unsigned_to_nat(31u);
v___x_1339_ = lean_unsigned_to_nat(160u);
v___x_1340_ = ((lean_object*)(l_Lean_Expr_updateForallS_x21___redArg___closed__0));
v___x_1341_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1342_ = l_mkPanicMessageWithDecl(v___x_1341_, v___x_1340_, v___x_1339_, v___x_1338_, v___x_1337_);
return v___x_1342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallS_x21___redArg(lean_object* v_inst_1343_, lean_object* v_inst_1344_, lean_object* v_e_1345_, lean_object* v_newDomain_1346_, lean_object* v_newBody_1347_){
_start:
{
if (lean_obj_tag(v_e_1345_) == 7)
{
lean_object* v_toApplicative_1348_; lean_object* v_toPure_1349_; lean_object* v_binderName_1350_; lean_object* v_binderType_1351_; lean_object* v_body_1352_; uint8_t v_binderInfo_1353_; size_t v___x_1354_; size_t v___x_1355_; uint8_t v___x_1356_; 
v_toApplicative_1348_ = lean_ctor_get(v_inst_1344_, 0);
v_toPure_1349_ = lean_ctor_get(v_toApplicative_1348_, 1);
v_binderName_1350_ = lean_ctor_get(v_e_1345_, 0);
v_binderType_1351_ = lean_ctor_get(v_e_1345_, 1);
v_body_1352_ = lean_ctor_get(v_e_1345_, 2);
v_binderInfo_1353_ = lean_ctor_get_uint8(v_e_1345_, sizeof(void*)*3 + 8);
v___x_1354_ = lean_ptr_addr(v_binderType_1351_);
v___x_1355_ = lean_ptr_addr(v_newDomain_1346_);
v___x_1356_ = lean_usize_dec_eq(v___x_1354_, v___x_1355_);
if (v___x_1356_ == 0)
{
lean_object* v___x_1357_; 
lean_inc(v_binderName_1350_);
lean_dec_ref_known(v_e_1345_, 3);
v___x_1357_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v_inst_1343_, v_inst_1344_, v_binderName_1350_, v_binderInfo_1353_, v_newDomain_1346_, v_newBody_1347_);
return v___x_1357_;
}
else
{
size_t v___x_1358_; size_t v___x_1359_; uint8_t v___x_1360_; 
v___x_1358_ = lean_ptr_addr(v_body_1352_);
v___x_1359_ = lean_ptr_addr(v_newBody_1347_);
v___x_1360_ = lean_usize_dec_eq(v___x_1358_, v___x_1359_);
if (v___x_1360_ == 0)
{
lean_object* v___x_1361_; 
lean_inc(v_binderName_1350_);
lean_dec_ref_known(v_e_1345_, 3);
v___x_1361_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v_inst_1343_, v_inst_1344_, v_binderName_1350_, v_binderInfo_1353_, v_newDomain_1346_, v_newBody_1347_);
return v___x_1361_;
}
else
{
lean_object* v___x_1362_; 
lean_inc(v_toPure_1349_);
lean_dec_ref(v_newBody_1347_);
lean_dec_ref(v_newDomain_1346_);
lean_dec_ref(v_inst_1344_);
lean_dec_ref(v_inst_1343_);
v___x_1362_ = lean_apply_2(v_toPure_1349_, lean_box(0), v_e_1345_);
return v___x_1362_;
}
}
}
else
{
lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; 
lean_dec_ref(v_newBody_1347_);
lean_dec_ref(v_newDomain_1346_);
lean_dec_ref(v_e_1345_);
lean_dec_ref(v_inst_1343_);
v___x_1363_ = l_Lean_instInhabitedExpr;
v___x_1364_ = l_instInhabitedOfMonad___redArg(v_inst_1344_, v___x_1363_);
v___x_1365_ = lean_obj_once(&l_Lean_Expr_updateForallS_x21___redArg___closed__2, &l_Lean_Expr_updateForallS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateForallS_x21___redArg___closed__2);
v___x_1366_ = l_panic___redArg(v___x_1364_, v___x_1365_);
lean_dec(v___x_1364_);
return v___x_1366_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallS_x21(lean_object* v_m_1367_, lean_object* v_inst_1368_, lean_object* v_inst_1369_, lean_object* v_e_1370_, lean_object* v_newDomain_1371_, lean_object* v_newBody_1372_){
_start:
{
if (lean_obj_tag(v_e_1370_) == 7)
{
lean_object* v_toApplicative_1373_; lean_object* v_toPure_1374_; lean_object* v_binderName_1375_; lean_object* v_binderType_1376_; lean_object* v_body_1377_; uint8_t v_binderInfo_1378_; size_t v___x_1379_; size_t v___x_1380_; uint8_t v___x_1381_; 
v_toApplicative_1373_ = lean_ctor_get(v_inst_1369_, 0);
v_toPure_1374_ = lean_ctor_get(v_toApplicative_1373_, 1);
v_binderName_1375_ = lean_ctor_get(v_e_1370_, 0);
v_binderType_1376_ = lean_ctor_get(v_e_1370_, 1);
v_body_1377_ = lean_ctor_get(v_e_1370_, 2);
v_binderInfo_1378_ = lean_ctor_get_uint8(v_e_1370_, sizeof(void*)*3 + 8);
v___x_1379_ = lean_ptr_addr(v_binderType_1376_);
v___x_1380_ = lean_ptr_addr(v_newDomain_1371_);
v___x_1381_ = lean_usize_dec_eq(v___x_1379_, v___x_1380_);
if (v___x_1381_ == 0)
{
lean_object* v___x_1382_; 
lean_inc(v_binderName_1375_);
lean_dec_ref_known(v_e_1370_, 3);
v___x_1382_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v_inst_1368_, v_inst_1369_, v_binderName_1375_, v_binderInfo_1378_, v_newDomain_1371_, v_newBody_1372_);
return v___x_1382_;
}
else
{
size_t v___x_1383_; size_t v___x_1384_; uint8_t v___x_1385_; 
v___x_1383_ = lean_ptr_addr(v_body_1377_);
v___x_1384_ = lean_ptr_addr(v_newBody_1372_);
v___x_1385_ = lean_usize_dec_eq(v___x_1383_, v___x_1384_);
if (v___x_1385_ == 0)
{
lean_object* v___x_1386_; 
lean_inc(v_binderName_1375_);
lean_dec_ref_known(v_e_1370_, 3);
v___x_1386_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v_inst_1368_, v_inst_1369_, v_binderName_1375_, v_binderInfo_1378_, v_newDomain_1371_, v_newBody_1372_);
return v___x_1386_;
}
else
{
lean_object* v___x_1387_; 
lean_inc(v_toPure_1374_);
lean_dec_ref(v_newBody_1372_);
lean_dec_ref(v_newDomain_1371_);
lean_dec_ref(v_inst_1369_);
lean_dec_ref(v_inst_1368_);
v___x_1387_ = lean_apply_2(v_toPure_1374_, lean_box(0), v_e_1370_);
return v___x_1387_;
}
}
}
else
{
lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; 
lean_dec_ref(v_newBody_1372_);
lean_dec_ref(v_newDomain_1371_);
lean_dec_ref(v_e_1370_);
lean_dec_ref(v_inst_1368_);
v___x_1388_ = l_Lean_instInhabitedExpr;
v___x_1389_ = l_instInhabitedOfMonad___redArg(v_inst_1369_, v___x_1388_);
v___x_1390_ = lean_obj_once(&l_Lean_Expr_updateForallS_x21___redArg___closed__2, &l_Lean_Expr_updateForallS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateForallS_x21___redArg___closed__2);
v___x_1391_ = l_panic___redArg(v___x_1389_, v___x_1390_);
lean_dec(v___x_1389_);
return v___x_1391_;
}
}
}
static lean_object* _init_l_Lean_Expr_updateLambdaS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; 
v___x_1394_ = ((lean_object*)(l_Lean_Expr_updateLambdaS_x21___redArg___closed__1));
v___x_1395_ = lean_unsigned_to_nat(27u);
v___x_1396_ = lean_unsigned_to_nat(167u);
v___x_1397_ = ((lean_object*)(l_Lean_Expr_updateLambdaS_x21___redArg___closed__0));
v___x_1398_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1399_ = l_mkPanicMessageWithDecl(v___x_1398_, v___x_1397_, v___x_1396_, v___x_1395_, v___x_1394_);
return v___x_1399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLambdaS_x21___redArg(lean_object* v_inst_1400_, lean_object* v_inst_1401_, lean_object* v_e_1402_, lean_object* v_newDomain_1403_, lean_object* v_newBody_1404_){
_start:
{
if (lean_obj_tag(v_e_1402_) == 6)
{
lean_object* v_toApplicative_1405_; lean_object* v_toPure_1406_; lean_object* v_binderName_1407_; lean_object* v_binderType_1408_; lean_object* v_body_1409_; uint8_t v_binderInfo_1410_; size_t v___x_1411_; size_t v___x_1412_; uint8_t v___x_1413_; 
v_toApplicative_1405_ = lean_ctor_get(v_inst_1401_, 0);
v_toPure_1406_ = lean_ctor_get(v_toApplicative_1405_, 1);
v_binderName_1407_ = lean_ctor_get(v_e_1402_, 0);
v_binderType_1408_ = lean_ctor_get(v_e_1402_, 1);
v_body_1409_ = lean_ctor_get(v_e_1402_, 2);
v_binderInfo_1410_ = lean_ctor_get_uint8(v_e_1402_, sizeof(void*)*3 + 8);
v___x_1411_ = lean_ptr_addr(v_binderType_1408_);
v___x_1412_ = lean_ptr_addr(v_newDomain_1403_);
v___x_1413_ = lean_usize_dec_eq(v___x_1411_, v___x_1412_);
if (v___x_1413_ == 0)
{
lean_object* v___x_1414_; 
lean_inc(v_binderName_1407_);
lean_dec_ref_known(v_e_1402_, 3);
v___x_1414_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v_inst_1400_, v_inst_1401_, v_binderName_1407_, v_binderInfo_1410_, v_newDomain_1403_, v_newBody_1404_);
return v___x_1414_;
}
else
{
size_t v___x_1415_; size_t v___x_1416_; uint8_t v___x_1417_; 
v___x_1415_ = lean_ptr_addr(v_body_1409_);
v___x_1416_ = lean_ptr_addr(v_newBody_1404_);
v___x_1417_ = lean_usize_dec_eq(v___x_1415_, v___x_1416_);
if (v___x_1417_ == 0)
{
lean_object* v___x_1418_; 
lean_inc(v_binderName_1407_);
lean_dec_ref_known(v_e_1402_, 3);
v___x_1418_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v_inst_1400_, v_inst_1401_, v_binderName_1407_, v_binderInfo_1410_, v_newDomain_1403_, v_newBody_1404_);
return v___x_1418_;
}
else
{
lean_object* v___x_1419_; 
lean_inc(v_toPure_1406_);
lean_dec_ref(v_newBody_1404_);
lean_dec_ref(v_newDomain_1403_);
lean_dec_ref(v_inst_1401_);
lean_dec_ref(v_inst_1400_);
v___x_1419_ = lean_apply_2(v_toPure_1406_, lean_box(0), v_e_1402_);
return v___x_1419_;
}
}
}
else
{
lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; 
lean_dec_ref(v_newBody_1404_);
lean_dec_ref(v_newDomain_1403_);
lean_dec_ref(v_e_1402_);
lean_dec_ref(v_inst_1400_);
v___x_1420_ = l_Lean_instInhabitedExpr;
v___x_1421_ = l_instInhabitedOfMonad___redArg(v_inst_1401_, v___x_1420_);
v___x_1422_ = lean_obj_once(&l_Lean_Expr_updateLambdaS_x21___redArg___closed__2, &l_Lean_Expr_updateLambdaS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateLambdaS_x21___redArg___closed__2);
v___x_1423_ = l_panic___redArg(v___x_1421_, v___x_1422_);
lean_dec(v___x_1421_);
return v___x_1423_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLambdaS_x21(lean_object* v_m_1424_, lean_object* v_inst_1425_, lean_object* v_inst_1426_, lean_object* v_e_1427_, lean_object* v_newDomain_1428_, lean_object* v_newBody_1429_){
_start:
{
if (lean_obj_tag(v_e_1427_) == 6)
{
lean_object* v_toApplicative_1430_; lean_object* v_toPure_1431_; lean_object* v_binderName_1432_; lean_object* v_binderType_1433_; lean_object* v_body_1434_; uint8_t v_binderInfo_1435_; size_t v___x_1436_; size_t v___x_1437_; uint8_t v___x_1438_; 
v_toApplicative_1430_ = lean_ctor_get(v_inst_1426_, 0);
v_toPure_1431_ = lean_ctor_get(v_toApplicative_1430_, 1);
v_binderName_1432_ = lean_ctor_get(v_e_1427_, 0);
v_binderType_1433_ = lean_ctor_get(v_e_1427_, 1);
v_body_1434_ = lean_ctor_get(v_e_1427_, 2);
v_binderInfo_1435_ = lean_ctor_get_uint8(v_e_1427_, sizeof(void*)*3 + 8);
v___x_1436_ = lean_ptr_addr(v_binderType_1433_);
v___x_1437_ = lean_ptr_addr(v_newDomain_1428_);
v___x_1438_ = lean_usize_dec_eq(v___x_1436_, v___x_1437_);
if (v___x_1438_ == 0)
{
lean_object* v___x_1439_; 
lean_inc(v_binderName_1432_);
lean_dec_ref_known(v_e_1427_, 3);
v___x_1439_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v_inst_1425_, v_inst_1426_, v_binderName_1432_, v_binderInfo_1435_, v_newDomain_1428_, v_newBody_1429_);
return v___x_1439_;
}
else
{
size_t v___x_1440_; size_t v___x_1441_; uint8_t v___x_1442_; 
v___x_1440_ = lean_ptr_addr(v_body_1434_);
v___x_1441_ = lean_ptr_addr(v_newBody_1429_);
v___x_1442_ = lean_usize_dec_eq(v___x_1440_, v___x_1441_);
if (v___x_1442_ == 0)
{
lean_object* v___x_1443_; 
lean_inc(v_binderName_1432_);
lean_dec_ref_known(v_e_1427_, 3);
v___x_1443_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v_inst_1425_, v_inst_1426_, v_binderName_1432_, v_binderInfo_1435_, v_newDomain_1428_, v_newBody_1429_);
return v___x_1443_;
}
else
{
lean_object* v___x_1444_; 
lean_inc(v_toPure_1431_);
lean_dec_ref(v_newBody_1429_);
lean_dec_ref(v_newDomain_1428_);
lean_dec_ref(v_inst_1426_);
lean_dec_ref(v_inst_1425_);
v___x_1444_ = lean_apply_2(v_toPure_1431_, lean_box(0), v_e_1427_);
return v___x_1444_;
}
}
}
else
{
lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; 
lean_dec_ref(v_newBody_1429_);
lean_dec_ref(v_newDomain_1428_);
lean_dec_ref(v_e_1427_);
lean_dec_ref(v_inst_1425_);
v___x_1445_ = l_Lean_instInhabitedExpr;
v___x_1446_ = l_instInhabitedOfMonad___redArg(v_inst_1426_, v___x_1445_);
v___x_1447_ = lean_obj_once(&l_Lean_Expr_updateLambdaS_x21___redArg___closed__2, &l_Lean_Expr_updateLambdaS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateLambdaS_x21___redArg___closed__2);
v___x_1448_ = l_panic___redArg(v___x_1446_, v___x_1447_);
lean_dec(v___x_1446_);
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
lean_object* v_toApplicative_1463_; lean_object* v_toPure_1464_; lean_object* v_declName_1465_; lean_object* v_type_1466_; lean_object* v_value_1467_; lean_object* v_body_1468_; uint8_t v_nondep_1469_; size_t v___x_1470_; size_t v___x_1471_; uint8_t v___x_1472_; 
v_toApplicative_1463_ = lean_ctor_get(v_inst_1458_, 0);
v_toPure_1464_ = lean_ctor_get(v_toApplicative_1463_, 1);
v_declName_1465_ = lean_ctor_get(v_e_1459_, 0);
v_type_1466_ = lean_ctor_get(v_e_1459_, 1);
v_value_1467_ = lean_ctor_get(v_e_1459_, 2);
v_body_1468_ = lean_ctor_get(v_e_1459_, 3);
v_nondep_1469_ = lean_ctor_get_uint8(v_e_1459_, sizeof(void*)*4 + 8);
v___x_1470_ = lean_ptr_addr(v_type_1466_);
v___x_1471_ = lean_ptr_addr(v_newType_1460_);
v___x_1472_ = lean_usize_dec_eq(v___x_1470_, v___x_1471_);
if (v___x_1472_ == 0)
{
lean_object* v___x_1473_; 
lean_inc(v_declName_1465_);
lean_dec_ref_known(v_e_1459_, 4);
v___x_1473_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1457_, v_inst_1458_, v_declName_1465_, v_newType_1460_, v_newVal_1461_, v_newBody_1462_, v_nondep_1469_);
return v___x_1473_;
}
else
{
size_t v___x_1474_; size_t v___x_1475_; uint8_t v___x_1476_; 
v___x_1474_ = lean_ptr_addr(v_value_1467_);
v___x_1475_ = lean_ptr_addr(v_newVal_1461_);
v___x_1476_ = lean_usize_dec_eq(v___x_1474_, v___x_1475_);
if (v___x_1476_ == 0)
{
lean_object* v___x_1477_; 
lean_inc(v_declName_1465_);
lean_dec_ref_known(v_e_1459_, 4);
v___x_1477_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1457_, v_inst_1458_, v_declName_1465_, v_newType_1460_, v_newVal_1461_, v_newBody_1462_, v_nondep_1469_);
return v___x_1477_;
}
else
{
size_t v___x_1478_; size_t v___x_1479_; uint8_t v___x_1480_; 
v___x_1478_ = lean_ptr_addr(v_body_1468_);
v___x_1479_ = lean_ptr_addr(v_newBody_1462_);
v___x_1480_ = lean_usize_dec_eq(v___x_1478_, v___x_1479_);
if (v___x_1480_ == 0)
{
lean_object* v___x_1481_; 
lean_inc(v_declName_1465_);
lean_dec_ref_known(v_e_1459_, 4);
v___x_1481_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1457_, v_inst_1458_, v_declName_1465_, v_newType_1460_, v_newVal_1461_, v_newBody_1462_, v_nondep_1469_);
return v___x_1481_;
}
else
{
lean_object* v___x_1482_; 
lean_inc(v_toPure_1464_);
lean_dec_ref(v_newBody_1462_);
lean_dec_ref(v_newVal_1461_);
lean_dec_ref(v_newType_1460_);
lean_dec_ref(v_inst_1458_);
lean_dec_ref(v_inst_1457_);
v___x_1482_ = lean_apply_2(v_toPure_1464_, lean_box(0), v_e_1459_);
return v___x_1482_;
}
}
}
}
else
{
lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; 
lean_dec_ref(v_newBody_1462_);
lean_dec_ref(v_newVal_1461_);
lean_dec_ref(v_newType_1460_);
lean_dec_ref(v_e_1459_);
lean_dec_ref(v_inst_1457_);
v___x_1483_ = l_Lean_instInhabitedExpr;
v___x_1484_ = l_instInhabitedOfMonad___redArg(v_inst_1458_, v___x_1483_);
v___x_1485_ = lean_obj_once(&l_Lean_Expr_updateLetS_x21___redArg___closed__2, &l_Lean_Expr_updateLetS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateLetS_x21___redArg___closed__2);
v___x_1486_ = l_panic___redArg(v___x_1484_, v___x_1485_);
lean_dec(v___x_1484_);
return v___x_1486_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLetS_x21(lean_object* v_m_1487_, lean_object* v_inst_1488_, lean_object* v_inst_1489_, lean_object* v_e_1490_, lean_object* v_newType_1491_, lean_object* v_newVal_1492_, lean_object* v_newBody_1493_){
_start:
{
if (lean_obj_tag(v_e_1490_) == 8)
{
lean_object* v_toApplicative_1494_; lean_object* v_toPure_1495_; lean_object* v_declName_1496_; lean_object* v_type_1497_; lean_object* v_value_1498_; lean_object* v_body_1499_; uint8_t v_nondep_1500_; size_t v___x_1501_; size_t v___x_1502_; uint8_t v___x_1503_; 
v_toApplicative_1494_ = lean_ctor_get(v_inst_1489_, 0);
v_toPure_1495_ = lean_ctor_get(v_toApplicative_1494_, 1);
v_declName_1496_ = lean_ctor_get(v_e_1490_, 0);
v_type_1497_ = lean_ctor_get(v_e_1490_, 1);
v_value_1498_ = lean_ctor_get(v_e_1490_, 2);
v_body_1499_ = lean_ctor_get(v_e_1490_, 3);
v_nondep_1500_ = lean_ctor_get_uint8(v_e_1490_, sizeof(void*)*4 + 8);
v___x_1501_ = lean_ptr_addr(v_type_1497_);
v___x_1502_ = lean_ptr_addr(v_newType_1491_);
v___x_1503_ = lean_usize_dec_eq(v___x_1501_, v___x_1502_);
if (v___x_1503_ == 0)
{
lean_object* v___x_1504_; 
lean_inc(v_declName_1496_);
lean_dec_ref_known(v_e_1490_, 4);
v___x_1504_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1488_, v_inst_1489_, v_declName_1496_, v_newType_1491_, v_newVal_1492_, v_newBody_1493_, v_nondep_1500_);
return v___x_1504_;
}
else
{
size_t v___x_1505_; size_t v___x_1506_; uint8_t v___x_1507_; 
v___x_1505_ = lean_ptr_addr(v_value_1498_);
v___x_1506_ = lean_ptr_addr(v_newVal_1492_);
v___x_1507_ = lean_usize_dec_eq(v___x_1505_, v___x_1506_);
if (v___x_1507_ == 0)
{
lean_object* v___x_1508_; 
lean_inc(v_declName_1496_);
lean_dec_ref_known(v_e_1490_, 4);
v___x_1508_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1488_, v_inst_1489_, v_declName_1496_, v_newType_1491_, v_newVal_1492_, v_newBody_1493_, v_nondep_1500_);
return v___x_1508_;
}
else
{
size_t v___x_1509_; size_t v___x_1510_; uint8_t v___x_1511_; 
v___x_1509_ = lean_ptr_addr(v_body_1499_);
v___x_1510_ = lean_ptr_addr(v_newBody_1493_);
v___x_1511_ = lean_usize_dec_eq(v___x_1509_, v___x_1510_);
if (v___x_1511_ == 0)
{
lean_object* v___x_1512_; 
lean_inc(v_declName_1496_);
lean_dec_ref_known(v_e_1490_, 4);
v___x_1512_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1488_, v_inst_1489_, v_declName_1496_, v_newType_1491_, v_newVal_1492_, v_newBody_1493_, v_nondep_1500_);
return v___x_1512_;
}
else
{
lean_object* v___x_1513_; 
lean_inc(v_toPure_1495_);
lean_dec_ref(v_newBody_1493_);
lean_dec_ref(v_newVal_1492_);
lean_dec_ref(v_newType_1491_);
lean_dec_ref(v_inst_1489_);
lean_dec_ref(v_inst_1488_);
v___x_1513_ = lean_apply_2(v_toPure_1495_, lean_box(0), v_e_1490_);
return v___x_1513_;
}
}
}
}
else
{
lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; 
lean_dec_ref(v_newBody_1493_);
lean_dec_ref(v_newVal_1492_);
lean_dec_ref(v_newType_1491_);
lean_dec_ref(v_e_1490_);
lean_dec_ref(v_inst_1488_);
v___x_1514_ = l_Lean_instInhabitedExpr;
v___x_1515_ = l_instInhabitedOfMonad___redArg(v_inst_1489_, v___x_1514_);
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
lean_object* v_toApplicative_1831_; lean_object* v_toBind_1832_; lean_object* v_toPure_1833_; uint8_t v___x_1834_; 
v_toApplicative_1831_ = lean_ctor_get(v_inst_1826_, 0);
v_toBind_1832_ = lean_ctor_get(v_inst_1826_, 1);
lean_inc(v_toBind_1832_);
v_toPure_1833_ = lean_ctor_get(v_toApplicative_1831_, 1);
v___x_1834_ = lean_nat_dec_le(v_endIdx_1828_, v_i_1830_);
if (v___x_1834_ == 0)
{
lean_object* v___f_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; 
lean_inc_ref(v_args_1827_);
lean_inc_ref(v_inst_1826_);
lean_inc_ref(v_inst_1825_);
lean_inc(v_i_1830_);
v___f_1835_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1835_, 0, v_i_1830_);
lean_closure_set(v___f_1835_, 1, v_inst_1825_);
lean_closure_set(v___f_1835_, 2, v_inst_1826_);
lean_closure_set(v___f_1835_, 3, v_args_1827_);
lean_closure_set(v___f_1835_, 4, v_endIdx_1828_);
v___x_1836_ = l_Lean_instInhabitedExpr;
v___x_1837_ = lean_array_get(v___x_1836_, v_args_1827_, v_i_1830_);
lean_dec(v_i_1830_);
lean_dec_ref(v_args_1827_);
v___x_1838_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1825_, v_inst_1826_, v_b_1829_, v___x_1837_);
v___x_1839_ = lean_apply_4(v_toBind_1832_, lean_box(0), lean_box(0), v___x_1838_, v___f_1835_);
return v___x_1839_;
}
else
{
lean_object* v___x_1840_; 
lean_inc(v_toPure_1833_);
lean_dec(v_toBind_1832_);
lean_dec(v_i_1830_);
lean_dec(v_endIdx_1828_);
lean_dec_ref(v_args_1827_);
lean_dec_ref(v_inst_1826_);
lean_dec_ref(v_inst_1825_);
v___x_1840_ = lean_apply_2(v_toPure_1833_, lean_box(0), v_b_1829_);
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
lean_object* v_toApplicative_1899_; lean_object* v_toBind_1900_; lean_object* v_toPure_1901_; uint8_t v___x_1902_; 
v_toApplicative_1899_ = lean_ctor_get(v_inst_1894_, 0);
v_toBind_1900_ = lean_ctor_get(v_inst_1894_, 1);
lean_inc(v_toBind_1900_);
v_toPure_1901_ = lean_ctor_get(v_toApplicative_1899_, 1);
v___x_1902_ = lean_nat_dec_le(v_i_1898_, v_start_1896_);
if (v___x_1902_ == 0)
{
lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v_i_1905_; lean_object* v___f_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; 
v___x_1903_ = l_Lean_instInhabitedExpr;
v___x_1904_ = lean_unsigned_to_nat(1u);
v_i_1905_ = lean_nat_sub(v_i_1898_, v___x_1904_);
lean_inc(v_i_1905_);
lean_inc_ref(v_revArgs_1895_);
lean_inc_ref(v_inst_1894_);
lean_inc_ref(v_inst_1893_);
v___f_1906_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1906_, 0, v_inst_1893_);
lean_closure_set(v___f_1906_, 1, v_inst_1894_);
lean_closure_set(v___f_1906_, 2, v_revArgs_1895_);
lean_closure_set(v___f_1906_, 3, v_start_1896_);
lean_closure_set(v___f_1906_, 4, v_i_1905_);
v___x_1907_ = lean_array_get(v___x_1903_, v_revArgs_1895_, v_i_1905_);
lean_dec(v_i_1905_);
lean_dec_ref(v_revArgs_1895_);
v___x_1908_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1893_, v_inst_1894_, v_b_1897_, v___x_1907_);
v___x_1909_ = lean_apply_4(v_toBind_1900_, lean_box(0), lean_box(0), v___x_1908_, v___f_1906_);
return v___x_1909_;
}
else
{
lean_object* v___x_1910_; 
lean_inc(v_toPure_1901_);
lean_dec(v_toBind_1900_);
lean_dec(v_start_1896_);
lean_dec_ref(v_revArgs_1895_);
lean_dec_ref(v_inst_1894_);
lean_dec_ref(v_inst_1893_);
v___x_1910_ = lean_apply_2(v_toPure_1901_, lean_box(0), v_b_1897_);
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
