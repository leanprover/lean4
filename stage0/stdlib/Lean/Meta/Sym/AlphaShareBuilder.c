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
size_t v_x_2068__boxed_189_; size_t v_x_2069__boxed_190_; lean_object* v_res_191_; 
v_x_2068__boxed_189_ = lean_unbox_usize(v_x_185_);
lean_dec(v_x_185_);
v_x_2069__boxed_190_ = lean_unbox_usize(v_x_186_);
lean_dec(v_x_186_);
v_res_191_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg(v_x_184_, v_x_2068__boxed_189_, v_x_2069__boxed_190_, v_x_187_, v_x_188_);
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
size_t v_x_2246__boxed_238_; lean_object* v_res_239_; 
v_x_2246__boxed_238_ = lean_unbox_usize(v_x_235_);
lean_dec(v_x_235_);
v_res_239_ = l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg(v_x_234_, v_x_2246__boxed_238_, v_x_236_, v_x_237_);
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
size_t v_x_2344__boxed_312_; lean_object* v_res_313_; 
v_x_2344__boxed_312_ = lean_unbox_usize(v_x_309_);
lean_dec(v_x_309_);
v_res_313_ = l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0(v_00_u03b2_307_, v_x_308_, v_x_2344__boxed_312_, v_x_310_, v_x_311_);
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
size_t v_x_2368__boxed_348_; size_t v_x_2369__boxed_349_; lean_object* v_res_350_; 
v_x_2368__boxed_348_ = lean_unbox_usize(v_x_344_);
lean_dec(v_x_344_);
v_x_2369__boxed_349_ = lean_unbox_usize(v_x_345_);
lean_dec(v_x_345_);
v_res_350_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2(v_00_u03b2_342_, v_x_343_, v_x_2368__boxed_348_, v_x_2369__boxed_349_, v_x_346_, v_x_347_);
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
v___x_379_ = l_Lean_Meta_Sym_instInhabitedSymM___redArg();
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
static lean_object* _init_l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2(void){
_start:
{
lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_449_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__1));
v___x_450_ = lean_unsigned_to_nat(16u);
v___x_451_ = lean_unsigned_to_nat(62u);
v___x_452_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__0));
v___x_453_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_454_ = l_mkPanicMessageWithDecl(v___x_453_, v___x_452_, v___x_451_, v___x_450_, v___x_449_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM___redArg(lean_object* v_k_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_){
_start:
{
lean_object* v___x_463_; lean_object* v___x_464_; uint8_t v_debug_465_; lean_object* v___x_466_; lean_object* v_env_467_; lean_object* v___x_468_; lean_object* v___x_469_; uint8_t v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_463_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0, &l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0);
v___x_464_ = lean_st_ref_get(v_a_457_);
v_debug_465_ = lean_ctor_get_uint8(v___x_464_, sizeof(void*)*11);
lean_dec(v___x_464_);
v___x_466_ = lean_st_ref_get(v_a_461_);
v_env_467_ = lean_ctor_get(v___x_466_, 0);
lean_inc_ref(v_env_467_);
lean_dec(v___x_466_);
v___x_468_ = lean_box(v_debug_465_);
v___x_469_ = lean_apply_1(v_k_455_, v___x_468_);
v___x_470_ = 0;
v___x_471_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_471_, 0, v_env_467_);
lean_ctor_set_uint8(v___x_471_, sizeof(void*)*1, v___x_470_);
lean_ctor_set_uint8(v___x_471_, sizeof(void*)*1 + 1, v___x_470_);
v___x_472_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___x_469_, v___x_471_, v_a_457_);
if (lean_obj_tag(v___x_472_) == 0)
{
lean_object* v_a_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_484_; 
v_a_473_ = lean_ctor_get(v___x_472_, 0);
v_isSharedCheck_484_ = !lean_is_exclusive(v___x_472_);
if (v_isSharedCheck_484_ == 0)
{
v___x_475_ = v___x_472_;
v_isShared_476_ = v_isSharedCheck_484_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_a_473_);
lean_dec(v___x_472_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_484_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
if (lean_obj_tag(v_a_473_) == 0)
{
lean_object* v___x_477_; lean_object* v___x_1314__overap_478_; lean_object* v___x_479_; 
lean_dec_ref_known(v_a_473_, 1);
lean_del_object(v___x_475_);
v___x_477_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2, &l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2_once, _init_l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2);
v___x_1314__overap_478_ = l_panic___redArg(v___x_463_, v___x_477_);
lean_inc(v_a_461_);
lean_inc_ref(v_a_460_);
lean_inc(v_a_459_);
lean_inc_ref(v_a_458_);
lean_inc(v_a_457_);
lean_inc_ref(v_a_456_);
v___x_479_ = lean_apply_7(v___x_1314__overap_478_, v_a_456_, v_a_457_, v_a_458_, v_a_459_, v_a_460_, v_a_461_, lean_box(0));
return v___x_479_;
}
else
{
lean_object* v_a_480_; lean_object* v___x_482_; 
v_a_480_ = lean_ctor_get(v_a_473_, 0);
lean_inc(v_a_480_);
lean_dec_ref_known(v_a_473_, 1);
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 0, v_a_480_);
v___x_482_ = v___x_475_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v_a_480_);
v___x_482_ = v_reuseFailAlloc_483_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
return v___x_482_;
}
}
}
}
else
{
lean_object* v_a_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_492_; 
v_a_485_ = lean_ctor_get(v___x_472_, 0);
v_isSharedCheck_492_ = !lean_is_exclusive(v___x_472_);
if (v_isSharedCheck_492_ == 0)
{
v___x_487_ = v___x_472_;
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_a_485_);
lean_dec(v___x_472_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v___x_490_; 
if (v_isShared_488_ == 0)
{
v___x_490_ = v___x_487_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v_a_485_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
return v___x_490_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___boxed(lean_object* v_k_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_Lean_Meta_Sym_Internal_liftBuilderM___redArg(v_k_493_, v_a_494_, v_a_495_, v_a_496_, v_a_497_, v_a_498_, v_a_499_);
lean_dec(v_a_499_);
lean_dec_ref(v_a_498_);
lean_dec(v_a_497_);
lean_dec_ref(v_a_496_);
lean_dec(v_a_495_);
lean_dec_ref(v_a_494_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM(lean_object* v_00_u03b1_502_, lean_object* v_k_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_){
_start:
{
lean_object* v___x_511_; lean_object* v___x_512_; uint8_t v_debug_513_; lean_object* v___x_514_; lean_object* v_env_515_; lean_object* v___x_516_; lean_object* v___x_517_; uint8_t v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_511_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0, &l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0);
v___x_512_ = lean_st_ref_get(v_a_505_);
v_debug_513_ = lean_ctor_get_uint8(v___x_512_, sizeof(void*)*11);
lean_dec(v___x_512_);
v___x_514_ = lean_st_ref_get(v_a_509_);
v_env_515_ = lean_ctor_get(v___x_514_, 0);
lean_inc_ref(v_env_515_);
lean_dec(v___x_514_);
v___x_516_ = lean_box(v_debug_513_);
v___x_517_ = lean_apply_1(v_k_503_, v___x_516_);
v___x_518_ = 0;
v___x_519_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_519_, 0, v_env_515_);
lean_ctor_set_uint8(v___x_519_, sizeof(void*)*1, v___x_518_);
lean_ctor_set_uint8(v___x_519_, sizeof(void*)*1 + 1, v___x_518_);
v___x_520_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___x_517_, v___x_519_, v_a_505_);
if (lean_obj_tag(v___x_520_) == 0)
{
lean_object* v_a_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_532_; 
v_a_521_ = lean_ctor_get(v___x_520_, 0);
v_isSharedCheck_532_ = !lean_is_exclusive(v___x_520_);
if (v_isSharedCheck_532_ == 0)
{
v___x_523_ = v___x_520_;
v_isShared_524_ = v_isSharedCheck_532_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_a_521_);
lean_dec(v___x_520_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_532_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
if (lean_obj_tag(v_a_521_) == 0)
{
lean_object* v___x_525_; lean_object* v___x_1337__overap_526_; lean_object* v___x_527_; 
lean_dec_ref_known(v_a_521_, 1);
lean_del_object(v___x_523_);
v___x_525_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2, &l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2_once, _init_l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2);
v___x_1337__overap_526_ = l_panic___redArg(v___x_511_, v___x_525_);
lean_inc(v_a_509_);
lean_inc_ref(v_a_508_);
lean_inc(v_a_507_);
lean_inc_ref(v_a_506_);
lean_inc(v_a_505_);
lean_inc_ref(v_a_504_);
v___x_527_ = lean_apply_7(v___x_1337__overap_526_, v_a_504_, v_a_505_, v_a_506_, v_a_507_, v_a_508_, v_a_509_, lean_box(0));
return v___x_527_;
}
else
{
lean_object* v_a_528_; lean_object* v___x_530_; 
v_a_528_ = lean_ctor_get(v_a_521_, 0);
lean_inc(v_a_528_);
lean_dec_ref_known(v_a_521_, 1);
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 0, v_a_528_);
v___x_530_ = v___x_523_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v_a_528_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
}
}
else
{
lean_object* v_a_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_540_; 
v_a_533_ = lean_ctor_get(v___x_520_, 0);
v_isSharedCheck_540_ = !lean_is_exclusive(v___x_520_);
if (v_isSharedCheck_540_ == 0)
{
v___x_535_ = v___x_520_;
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_a_533_);
lean_dec(v___x_520_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_538_; 
if (v_isShared_536_ == 0)
{
v___x_538_ = v___x_535_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_a_533_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
return v___x_538_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM___boxed(lean_object* v_00_u03b1_541_, lean_object* v_k_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l_Lean_Meta_Sym_Internal_liftBuilderM(v_00_u03b1_541_, v_k_542_, v_a_543_, v_a_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_);
lean_dec(v_a_548_);
lean_dec_ref(v_a_547_);
lean_dec(v_a_546_);
lean_dec_ref(v_a_545_);
lean_dec(v_a_544_);
lean_dec_ref(v_a_543_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_share1___redArg(lean_object* v_e_551_, lean_object* v_a_552_){
_start:
{
lean_object* v___x_553_; uint64_t v___x_554_; size_t v___x_555_; lean_object* v___x_556_; size_t v___x_557_; size_t v___x_558_; uint8_t v___x_559_; 
v___x_553_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy;
v___x_554_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_551_);
v___x_555_ = lean_uint64_to_usize(v___x_554_);
v___x_556_ = l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg(v_a_552_, v___x_555_, v_e_551_, v___x_553_);
v___x_557_ = lean_ptr_addr(v___x_556_);
v___x_558_ = lean_usize_once(&l_Lean_Meta_Sym_Internal_Sym_share1___redArg___closed__0, &l_Lean_Meta_Sym_Internal_Sym_share1___redArg___closed__0_once, _init_l_Lean_Meta_Sym_Internal_Sym_share1___redArg___closed__0);
v___x_559_ = lean_usize_dec_eq(v___x_557_, v___x_558_);
if (v___x_559_ == 0)
{
lean_object* v___x_560_; 
lean_dec_ref(v_e_551_);
v___x_560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_560_, 0, v___x_556_);
lean_ctor_set(v___x_560_, 1, v_a_552_);
return v___x_560_;
}
else
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
lean_dec_ref(v___x_556_);
v___x_561_ = lean_box(0);
lean_inc_ref(v_e_551_);
v___x_562_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1___redArg(v_a_552_, v_e_551_, v___x_561_);
v___x_563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_563_, 0, v_e_551_);
lean_ctor_set(v___x_563_, 1, v___x_562_);
return v___x_563_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_share1(lean_object* v_e_564_, uint8_t v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_){
_start:
{
lean_object* v___x_568_; 
v___x_568_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v_e_564_, v_a_567_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_share1___boxed(lean_object* v_e_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_){
_start:
{
uint8_t v_a_boxed_573_; lean_object* v_res_574_; 
v_a_boxed_573_ = lean_unbox(v_a_570_);
v_res_574_ = l_Lean_Meta_Sym_Internal_Builder_share1(v_e_569_, v_a_boxed_573_, v_a_571_, v_a_572_);
lean_dec_ref(v_a_571_);
return v_res_574_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__0(void){
_start:
{
lean_object* v___x_575_; 
v___x_575_ = l_Std_HashMap_instInhabited___redArg();
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1(lean_object* v_msg_576_, uint8_t v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_){
_start:
{
lean_object* v___x_580_; lean_object* v___f_581_; lean_object* v___f_582_; lean_object* v___f_583_; lean_object* v___x_534__overap_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_580_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__0, &l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__0);
v___f_581_ = lean_alloc_closure((void*)(l_EStateM_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_581_, 0, v___x_580_);
v___f_582_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_582_, 0, v___f_581_);
v___f_583_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_583_, 0, v___f_582_);
v___x_534__overap_584_ = lean_panic_fn_borrowed(v___f_583_, v_msg_576_);
lean_dec_ref(v___f_583_);
v___x_585_ = lean_box(v___y_577_);
lean_inc_ref(v___y_578_);
v___x_586_ = lean_apply_3(v___x_534__overap_584_, v___x_585_, v___y_578_, v___y_579_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___boxed(lean_object* v_msg_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_){
_start:
{
uint8_t v___y_635__boxed_591_; lean_object* v_res_592_; 
v___y_635__boxed_591_ = lean_unbox(v___y_588_);
v_res_592_ = l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1(v_msg_587_, v___y_635__boxed_591_, v___y_589_, v___y_590_);
lean_dec_ref(v___y_589_);
return v_res_592_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_593_, lean_object* v_i_594_, lean_object* v_k_595_){
_start:
{
lean_object* v___x_596_; uint8_t v___x_597_; 
v___x_596_ = lean_array_get_size(v_keys_593_);
v___x_597_ = lean_nat_dec_lt(v_i_594_, v___x_596_);
if (v___x_597_ == 0)
{
lean_dec(v_i_594_);
return v___x_597_;
}
else
{
lean_object* v_k_x27_598_; uint8_t v___x_599_; 
v_k_x27_598_ = lean_array_fget_borrowed(v_keys_593_, v_i_594_);
v___x_599_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_k_595_, v_k_x27_598_);
if (v___x_599_ == 0)
{
lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_600_ = lean_unsigned_to_nat(1u);
v___x_601_ = lean_nat_add(v_i_594_, v___x_600_);
lean_dec(v_i_594_);
v_i_594_ = v___x_601_;
goto _start;
}
else
{
lean_dec(v_i_594_);
return v___x_597_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_603_, lean_object* v_i_604_, lean_object* v_k_605_){
_start:
{
uint8_t v_res_606_; lean_object* v_r_607_; 
v_res_606_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg(v_keys_603_, v_i_604_, v_k_605_);
lean_dec_ref(v_k_605_);
lean_dec_ref(v_keys_603_);
v_r_607_ = lean_box(v_res_606_);
return v_r_607_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg(lean_object* v_x_608_, size_t v_x_609_, lean_object* v_x_610_){
_start:
{
if (lean_obj_tag(v_x_608_) == 0)
{
lean_object* v_es_611_; lean_object* v___x_612_; size_t v___x_613_; size_t v___x_614_; lean_object* v_j_615_; lean_object* v___x_616_; 
v_es_611_ = lean_ctor_get(v_x_608_, 0);
v___x_612_ = lean_box(2);
v___x_613_ = ((size_t)31ULL);
v___x_614_ = lean_usize_land(v_x_609_, v___x_613_);
v_j_615_ = lean_usize_to_nat(v___x_614_);
v___x_616_ = lean_array_get_borrowed(v___x_612_, v_es_611_, v_j_615_);
lean_dec(v_j_615_);
switch(lean_obj_tag(v___x_616_))
{
case 0:
{
lean_object* v_key_617_; uint8_t v___x_618_; 
v_key_617_ = lean_ctor_get(v___x_616_, 0);
v___x_618_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_610_, v_key_617_);
return v___x_618_;
}
case 1:
{
lean_object* v_node_619_; size_t v___x_620_; size_t v___x_621_; 
v_node_619_ = lean_ctor_get(v___x_616_, 0);
v___x_620_ = ((size_t)5ULL);
v___x_621_ = lean_usize_shift_right(v_x_609_, v___x_620_);
v_x_608_ = v_node_619_;
v_x_609_ = v___x_621_;
goto _start;
}
default: 
{
uint8_t v___x_623_; 
v___x_623_ = 0;
return v___x_623_;
}
}
}
else
{
lean_object* v_ks_624_; lean_object* v___x_625_; uint8_t v___x_626_; 
v_ks_624_ = lean_ctor_get(v_x_608_, 0);
v___x_625_ = lean_unsigned_to_nat(0u);
v___x_626_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg(v_ks_624_, v___x_625_, v_x_610_);
return v___x_626_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg___boxed(lean_object* v_x_627_, lean_object* v_x_628_, lean_object* v_x_629_){
_start:
{
size_t v_x_670__boxed_630_; uint8_t v_res_631_; lean_object* v_r_632_; 
v_x_670__boxed_630_ = lean_unbox_usize(v_x_628_);
lean_dec(v_x_628_);
v_res_631_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg(v_x_627_, v_x_670__boxed_630_, v_x_629_);
lean_dec_ref(v_x_629_);
lean_dec_ref(v_x_627_);
v_r_632_ = lean_box(v_res_631_);
return v_r_632_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg(lean_object* v_x_633_, lean_object* v_x_634_){
_start:
{
uint64_t v___x_635_; size_t v___x_636_; uint8_t v___x_637_; 
v___x_635_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_634_);
v___x_636_ = lean_uint64_to_usize(v___x_635_);
v___x_637_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg(v_x_633_, v___x_636_, v_x_634_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg___boxed(lean_object* v_x_638_, lean_object* v_x_639_){
_start:
{
uint8_t v_res_640_; lean_object* v_r_641_; 
v_res_640_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg(v_x_638_, v_x_639_);
lean_dec_ref(v_x_639_);
lean_dec_ref(v_x_638_);
v_r_641_ = lean_box(v_res_640_);
return v_r_641_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__2(void){
_start:
{
lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_644_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__1));
v___x_645_ = lean_unsigned_to_nat(2u);
v___x_646_ = lean_unsigned_to_nat(74u);
v___x_647_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__0));
v___x_648_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_649_ = l_mkPanicMessageWithDecl(v___x_648_, v___x_647_, v___x_646_, v___x_645_, v___x_644_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_assertShared(lean_object* v_e_650_, uint8_t v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_){
_start:
{
uint8_t v___x_654_; 
v___x_654_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg(v_a_653_, v_e_650_);
if (v___x_654_ == 0)
{
lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_655_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__2, &l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__2_once, _init_l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__2);
v___x_656_ = l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1(v___x_655_, v_a_651_, v_a_652_, v_a_653_);
return v___x_656_;
}
else
{
lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_657_ = lean_box(0);
v___x_658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_658_, 0, v___x_657_);
lean_ctor_set(v___x_658_, 1, v_a_653_);
return v___x_658_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_assertShared___boxed(lean_object* v_e_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_){
_start:
{
uint8_t v_a_boxed_663_; lean_object* v_res_664_; 
v_a_boxed_663_ = lean_unbox(v_a_660_);
v_res_664_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_e_659_, v_a_boxed_663_, v_a_661_, v_a_662_);
lean_dec_ref(v_a_661_);
lean_dec_ref(v_e_659_);
return v_res_664_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0(lean_object* v_00_u03b2_665_, lean_object* v_x_666_, lean_object* v_x_667_){
_start:
{
uint8_t v___x_668_; 
v___x_668_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg(v_x_666_, v_x_667_);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___boxed(lean_object* v_00_u03b2_669_, lean_object* v_x_670_, lean_object* v_x_671_){
_start:
{
uint8_t v_res_672_; lean_object* v_r_673_; 
v_res_672_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0(v_00_u03b2_669_, v_x_670_, v_x_671_);
lean_dec_ref(v_x_671_);
lean_dec_ref(v_x_670_);
v_r_673_ = lean_box(v_res_672_);
return v_r_673_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0(lean_object* v_00_u03b2_674_, lean_object* v_x_675_, size_t v_x_676_, lean_object* v_x_677_){
_start:
{
uint8_t v___x_678_; 
v___x_678_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg(v_x_675_, v_x_676_, v_x_677_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___boxed(lean_object* v_00_u03b2_679_, lean_object* v_x_680_, lean_object* v_x_681_, lean_object* v_x_682_){
_start:
{
size_t v_x_769__boxed_683_; uint8_t v_res_684_; lean_object* v_r_685_; 
v_x_769__boxed_683_ = lean_unbox_usize(v_x_681_);
lean_dec(v_x_681_);
v_res_684_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0(v_00_u03b2_679_, v_x_680_, v_x_769__boxed_683_, v_x_682_);
lean_dec_ref(v_x_682_);
lean_dec_ref(v_x_680_);
v_r_685_ = lean_box(v_res_684_);
return v_r_685_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_686_, lean_object* v_keys_687_, lean_object* v_vals_688_, lean_object* v_heq_689_, lean_object* v_i_690_, lean_object* v_k_691_){
_start:
{
uint8_t v___x_692_; 
v___x_692_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg(v_keys_687_, v_i_690_, v_k_691_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_693_, lean_object* v_keys_694_, lean_object* v_vals_695_, lean_object* v_heq_696_, lean_object* v_i_697_, lean_object* v_k_698_){
_start:
{
uint8_t v_res_699_; lean_object* v_r_700_; 
v_res_699_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2(v_00_u03b2_693_, v_keys_694_, v_vals_695_, v_heq_696_, v_i_697_, v_k_698_);
lean_dec_ref(v_k_698_);
lean_dec_ref(v_vals_695_);
lean_dec_ref(v_keys_694_);
v_r_700_ = lean_box(v_res_699_);
return v_r_700_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__10(void){
_start:
{
lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_720_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__9));
v___x_721_ = l_ReaderT_instMonad___redArg(v___x_720_);
return v___x_721_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__13(void){
_start:
{
lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_724_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__10, &l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__10_once, _init_l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__10);
v___x_725_ = lean_alloc_closure((void*)(l_ReaderT_read___boxed), 4, 3);
lean_closure_set(v___x_725_, 0, lean_box(0));
lean_closure_set(v___x_725_, 1, lean_box(0));
lean_closure_set(v___x_725_, 2, v___x_724_);
return v___x_725_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__14(void){
_start:
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_726_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__13, &l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__13_once, _init_l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__13);
v___x_727_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__12));
v___x_728_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__11));
v___x_729_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_729_, 0, v___x_728_);
lean_ctor_set(v___x_729_, 1, v___x_727_);
lean_ctor_set(v___x_729_, 2, v___x_726_);
return v___x_729_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM(void){
_start:
{
lean_object* v___x_730_; 
v___x_730_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__14, &l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__14_once, _init_l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__14);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLitS___redArg(lean_object* v_inst_731_, lean_object* v_l_732_){
_start:
{
lean_object* v_share1_733_; lean_object* v___x_734_; lean_object* v___x_735_; 
v_share1_733_ = lean_ctor_get(v_inst_731_, 0);
lean_inc(v_share1_733_);
lean_dec_ref(v_inst_731_);
v___x_734_ = l_Lean_Expr_lit___override(v_l_732_);
v___x_735_ = lean_apply_1(v_share1_733_, v___x_734_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLitS(lean_object* v_m_736_, lean_object* v_inst_737_, lean_object* v_l_738_){
_start:
{
lean_object* v___x_739_; 
v___x_739_ = l_Lean_Meta_Sym_Internal_mkLitS___redArg(v_inst_737_, v_l_738_);
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___redArg(lean_object* v_inst_740_, lean_object* v_declName_741_, lean_object* v_us_742_){
_start:
{
lean_object* v_share1_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
v_share1_743_ = lean_ctor_get(v_inst_740_, 0);
lean_inc(v_share1_743_);
lean_dec_ref(v_inst_740_);
v___x_744_ = l_Lean_Expr_const___override(v_declName_741_, v_us_742_);
v___x_745_ = lean_apply_1(v_share1_743_, v___x_744_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS(lean_object* v_m_746_, lean_object* v_inst_747_, lean_object* v_declName_748_, lean_object* v_us_749_){
_start:
{
lean_object* v___x_750_; 
v___x_750_ = l_Lean_Meta_Sym_Internal_mkConstS___redArg(v_inst_747_, v_declName_748_, v_us_749_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___redArg(lean_object* v_inst_751_, lean_object* v_idx_752_){
_start:
{
lean_object* v_share1_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
v_share1_753_ = lean_ctor_get(v_inst_751_, 0);
lean_inc(v_share1_753_);
lean_dec_ref(v_inst_751_);
v___x_754_ = l_Lean_Expr_bvar___override(v_idx_752_);
v___x_755_ = lean_apply_1(v_share1_753_, v___x_754_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS(lean_object* v_m_756_, lean_object* v_inst_757_, lean_object* v_idx_758_){
_start:
{
lean_object* v___x_759_; 
v___x_759_ = l_Lean_Meta_Sym_Internal_mkBVarS___redArg(v_inst_757_, v_idx_758_);
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS___redArg(lean_object* v_inst_760_, lean_object* v_u_761_){
_start:
{
lean_object* v_share1_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
v_share1_762_ = lean_ctor_get(v_inst_760_, 0);
lean_inc(v_share1_762_);
lean_dec_ref(v_inst_760_);
v___x_763_ = l_Lean_Expr_sort___override(v_u_761_);
v___x_764_ = lean_apply_1(v_share1_762_, v___x_763_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS(lean_object* v_m_765_, lean_object* v_inst_766_, lean_object* v_u_767_){
_start:
{
lean_object* v___x_768_; 
v___x_768_ = l_Lean_Meta_Sym_Internal_mkSortS___redArg(v_inst_766_, v_u_767_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___redArg(lean_object* v_inst_769_, lean_object* v_fvarId_770_){
_start:
{
lean_object* v_share1_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
v_share1_771_ = lean_ctor_get(v_inst_769_, 0);
lean_inc(v_share1_771_);
lean_dec_ref(v_inst_769_);
v___x_772_ = l_Lean_Expr_fvar___override(v_fvarId_770_);
v___x_773_ = lean_apply_1(v_share1_771_, v___x_772_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS(lean_object* v_m_774_, lean_object* v_inst_775_, lean_object* v_fvarId_776_){
_start:
{
lean_object* v___x_777_; 
v___x_777_ = l_Lean_Meta_Sym_Internal_mkFVarS___redArg(v_inst_775_, v_fvarId_776_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMVarS___redArg(lean_object* v_inst_778_, lean_object* v_mvarId_779_){
_start:
{
lean_object* v_share1_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
v_share1_780_ = lean_ctor_get(v_inst_778_, 0);
lean_inc(v_share1_780_);
lean_dec_ref(v_inst_778_);
v___x_781_ = l_Lean_Expr_mvar___override(v_mvarId_779_);
v___x_782_ = lean_apply_1(v_share1_780_, v___x_781_);
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMVarS(lean_object* v_m_783_, lean_object* v_inst_784_, lean_object* v_mvarId_785_){
_start:
{
lean_object* v___x_786_; 
v___x_786_ = l_Lean_Meta_Sym_Internal_mkMVarS___redArg(v_inst_784_, v_mvarId_785_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__0(lean_object* v_d_787_, lean_object* v_e_788_, lean_object* v_share1_789_, lean_object* v_____r_790_){
_start:
{
lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_791_ = l_Lean_Expr_mdata___override(v_d_787_, v_e_788_);
v___x_792_ = lean_apply_1(v_share1_789_, v___x_791_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1(lean_object* v___f_793_, lean_object* v_____r_794_){
_start:
{
lean_object* v___x_795_; 
v___x_795_ = lean_apply_1(v___f_793_, v_____r_794_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__2(lean_object* v___f_796_, lean_object* v_assertShared_797_, lean_object* v_e_798_, lean_object* v_toBind_799_, lean_object* v___f_800_, uint8_t v_____do__lift_801_){
_start:
{
if (v_____do__lift_801_ == 0)
{
lean_object* v___x_802_; lean_object* v___x_803_; 
lean_dec(v___f_800_);
lean_dec(v_toBind_799_);
lean_dec_ref(v_e_798_);
lean_dec(v_assertShared_797_);
v___x_802_ = lean_box(0);
v___x_803_ = lean_apply_1(v___f_796_, v___x_802_);
return v___x_803_;
}
else
{
lean_object* v___x_804_; lean_object* v___x_805_; 
lean_dec(v___f_796_);
v___x_804_ = lean_apply_1(v_assertShared_797_, v_e_798_);
v___x_805_ = lean_apply_4(v_toBind_799_, lean_box(0), lean_box(0), v___x_804_, v___f_800_);
return v___x_805_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__2___boxed(lean_object* v___f_806_, lean_object* v_assertShared_807_, lean_object* v_e_808_, lean_object* v_toBind_809_, lean_object* v___f_810_, lean_object* v_____do__lift_811_){
_start:
{
uint8_t v_____do__lift_63__boxed_812_; lean_object* v_res_813_; 
v_____do__lift_63__boxed_812_ = lean_unbox(v_____do__lift_811_);
v_res_813_ = l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__2(v___f_806_, v_assertShared_807_, v_e_808_, v_toBind_809_, v___f_810_, v_____do__lift_63__boxed_812_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg(lean_object* v_inst_814_, lean_object* v_inst_815_, lean_object* v_d_816_, lean_object* v_e_817_){
_start:
{
lean_object* v_toBind_818_; lean_object* v_share1_819_; lean_object* v_assertShared_820_; lean_object* v_isDebugEnabled_821_; lean_object* v___f_822_; lean_object* v___f_823_; lean_object* v___f_824_; lean_object* v___x_825_; 
v_toBind_818_ = lean_ctor_get(v_inst_815_, 1);
lean_inc_n(v_toBind_818_, 2);
lean_dec_ref(v_inst_815_);
v_share1_819_ = lean_ctor_get(v_inst_814_, 0);
lean_inc(v_share1_819_);
v_assertShared_820_ = lean_ctor_get(v_inst_814_, 1);
lean_inc(v_assertShared_820_);
v_isDebugEnabled_821_ = lean_ctor_get(v_inst_814_, 2);
lean_inc(v_isDebugEnabled_821_);
lean_dec_ref(v_inst_814_);
lean_inc_ref(v_e_817_);
v___f_822_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__0), 4, 3);
lean_closure_set(v___f_822_, 0, v_d_816_);
lean_closure_set(v___f_822_, 1, v_e_817_);
lean_closure_set(v___f_822_, 2, v_share1_819_);
lean_inc_ref(v___f_822_);
v___f_823_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_823_, 0, v___f_822_);
v___f_824_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_824_, 0, v___f_822_);
lean_closure_set(v___f_824_, 1, v_assertShared_820_);
lean_closure_set(v___f_824_, 2, v_e_817_);
lean_closure_set(v___f_824_, 3, v_toBind_818_);
lean_closure_set(v___f_824_, 4, v___f_823_);
v___x_825_ = lean_apply_4(v_toBind_818_, lean_box(0), lean_box(0), v_isDebugEnabled_821_, v___f_824_);
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS(lean_object* v_m_826_, lean_object* v_inst_827_, lean_object* v_inst_828_, lean_object* v_d_829_, lean_object* v_e_830_){
_start:
{
lean_object* v___x_831_; 
v___x_831_ = l_Lean_Meta_Sym_Internal_mkMDataS___redArg(v_inst_827_, v_inst_828_, v_d_829_, v_e_830_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__0(lean_object* v_structName_832_, lean_object* v_idx_833_, lean_object* v_struct_834_, lean_object* v_share1_835_, lean_object* v_____r_836_){
_start:
{
lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_837_ = l_Lean_Expr_proj___override(v_structName_832_, v_idx_833_, v_struct_834_);
v___x_838_ = lean_apply_1(v_share1_835_, v___x_837_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__2(lean_object* v___f_839_, lean_object* v_assertShared_840_, lean_object* v_struct_841_, lean_object* v_toBind_842_, lean_object* v___f_843_, uint8_t v_____do__lift_844_){
_start:
{
if (v_____do__lift_844_ == 0)
{
lean_object* v___x_845_; lean_object* v___x_846_; 
lean_dec(v___f_843_);
lean_dec(v_toBind_842_);
lean_dec_ref(v_struct_841_);
lean_dec(v_assertShared_840_);
v___x_845_ = lean_box(0);
v___x_846_ = lean_apply_1(v___f_839_, v___x_845_);
return v___x_846_;
}
else
{
lean_object* v___x_847_; lean_object* v___x_848_; 
lean_dec(v___f_839_);
v___x_847_ = lean_apply_1(v_assertShared_840_, v_struct_841_);
v___x_848_ = lean_apply_4(v_toBind_842_, lean_box(0), lean_box(0), v___x_847_, v___f_843_);
return v___x_848_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__2___boxed(lean_object* v___f_849_, lean_object* v_assertShared_850_, lean_object* v_struct_851_, lean_object* v_toBind_852_, lean_object* v___f_853_, lean_object* v_____do__lift_854_){
_start:
{
uint8_t v_____do__lift_57__boxed_855_; lean_object* v_res_856_; 
v_____do__lift_57__boxed_855_ = lean_unbox(v_____do__lift_854_);
v_res_856_ = l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__2(v___f_849_, v_assertShared_850_, v_struct_851_, v_toBind_852_, v___f_853_, v_____do__lift_57__boxed_855_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___redArg(lean_object* v_inst_857_, lean_object* v_inst_858_, lean_object* v_structName_859_, lean_object* v_idx_860_, lean_object* v_struct_861_){
_start:
{
lean_object* v_toBind_862_; lean_object* v_share1_863_; lean_object* v_assertShared_864_; lean_object* v_isDebugEnabled_865_; lean_object* v___f_866_; lean_object* v___f_867_; lean_object* v___f_868_; lean_object* v___x_869_; 
v_toBind_862_ = lean_ctor_get(v_inst_858_, 1);
lean_inc_n(v_toBind_862_, 2);
lean_dec_ref(v_inst_858_);
v_share1_863_ = lean_ctor_get(v_inst_857_, 0);
lean_inc(v_share1_863_);
v_assertShared_864_ = lean_ctor_get(v_inst_857_, 1);
lean_inc(v_assertShared_864_);
v_isDebugEnabled_865_ = lean_ctor_get(v_inst_857_, 2);
lean_inc(v_isDebugEnabled_865_);
lean_dec_ref(v_inst_857_);
lean_inc_ref(v_struct_861_);
v___f_866_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__0), 5, 4);
lean_closure_set(v___f_866_, 0, v_structName_859_);
lean_closure_set(v___f_866_, 1, v_idx_860_);
lean_closure_set(v___f_866_, 2, v_struct_861_);
lean_closure_set(v___f_866_, 3, v_share1_863_);
lean_inc_ref(v___f_866_);
v___f_867_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_867_, 0, v___f_866_);
v___f_868_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_868_, 0, v___f_866_);
lean_closure_set(v___f_868_, 1, v_assertShared_864_);
lean_closure_set(v___f_868_, 2, v_struct_861_);
lean_closure_set(v___f_868_, 3, v_toBind_862_);
lean_closure_set(v___f_868_, 4, v___f_867_);
v___x_869_ = lean_apply_4(v_toBind_862_, lean_box(0), lean_box(0), v_isDebugEnabled_865_, v___f_868_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS(lean_object* v_m_870_, lean_object* v_inst_871_, lean_object* v_inst_872_, lean_object* v_structName_873_, lean_object* v_idx_874_, lean_object* v_struct_875_){
_start:
{
lean_object* v___x_876_; 
v___x_876_ = l_Lean_Meta_Sym_Internal_mkProjS___redArg(v_inst_871_, v_inst_872_, v_structName_873_, v_idx_874_, v_struct_875_);
return v___x_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__0(lean_object* v_f_877_, lean_object* v_a_878_, lean_object* v_share1_879_, lean_object* v_____r_880_){
_start:
{
lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_881_ = l_Lean_Expr_app___override(v_f_877_, v_a_878_);
v___x_882_ = lean_apply_1(v_share1_879_, v___x_881_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__2(lean_object* v_assertShared_883_, lean_object* v_a_884_, lean_object* v_toBind_885_, lean_object* v___f_886_, lean_object* v_____r_887_){
_start:
{
lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_888_ = lean_apply_1(v_assertShared_883_, v_a_884_);
v___x_889_ = lean_apply_4(v_toBind_885_, lean_box(0), lean_box(0), v___x_888_, v___f_886_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__1(lean_object* v___f_890_, lean_object* v_assertShared_891_, lean_object* v_a_892_, lean_object* v_toBind_893_, lean_object* v___f_894_, lean_object* v_f_895_, uint8_t v_____do__lift_896_){
_start:
{
if (v_____do__lift_896_ == 0)
{
lean_object* v___x_897_; lean_object* v___x_898_; 
lean_dec_ref(v_f_895_);
lean_dec(v___f_894_);
lean_dec(v_toBind_893_);
lean_dec_ref(v_a_892_);
lean_dec(v_assertShared_891_);
v___x_897_ = lean_box(0);
v___x_898_ = lean_apply_1(v___f_890_, v___x_897_);
return v___x_898_;
}
else
{
lean_object* v___f_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
lean_dec(v___f_890_);
lean_inc(v_toBind_893_);
lean_inc(v_assertShared_891_);
v___f_899_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__2), 5, 4);
lean_closure_set(v___f_899_, 0, v_assertShared_891_);
lean_closure_set(v___f_899_, 1, v_a_892_);
lean_closure_set(v___f_899_, 2, v_toBind_893_);
lean_closure_set(v___f_899_, 3, v___f_894_);
v___x_900_ = lean_apply_1(v_assertShared_891_, v_f_895_);
v___x_901_ = lean_apply_4(v_toBind_893_, lean_box(0), lean_box(0), v___x_900_, v___f_899_);
return v___x_901_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__1___boxed(lean_object* v___f_902_, lean_object* v_assertShared_903_, lean_object* v_a_904_, lean_object* v_toBind_905_, lean_object* v___f_906_, lean_object* v_f_907_, lean_object* v_____do__lift_908_){
_start:
{
uint8_t v_____do__lift_74__boxed_909_; lean_object* v_res_910_; 
v_____do__lift_74__boxed_909_ = lean_unbox(v_____do__lift_908_);
v_res_910_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__1(v___f_902_, v_assertShared_903_, v_a_904_, v_toBind_905_, v___f_906_, v_f_907_, v_____do__lift_74__boxed_909_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg(lean_object* v_inst_911_, lean_object* v_inst_912_, lean_object* v_f_913_, lean_object* v_a_914_){
_start:
{
lean_object* v_toBind_915_; lean_object* v_share1_916_; lean_object* v_assertShared_917_; lean_object* v_isDebugEnabled_918_; lean_object* v___f_919_; lean_object* v___f_920_; lean_object* v___f_921_; lean_object* v___x_922_; 
v_toBind_915_ = lean_ctor_get(v_inst_912_, 1);
lean_inc_n(v_toBind_915_, 2);
lean_dec_ref(v_inst_912_);
v_share1_916_ = lean_ctor_get(v_inst_911_, 0);
lean_inc(v_share1_916_);
v_assertShared_917_ = lean_ctor_get(v_inst_911_, 1);
lean_inc(v_assertShared_917_);
v_isDebugEnabled_918_ = lean_ctor_get(v_inst_911_, 2);
lean_inc(v_isDebugEnabled_918_);
lean_dec_ref(v_inst_911_);
lean_inc_ref(v_a_914_);
lean_inc_ref(v_f_913_);
v___f_919_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__0), 4, 3);
lean_closure_set(v___f_919_, 0, v_f_913_);
lean_closure_set(v___f_919_, 1, v_a_914_);
lean_closure_set(v___f_919_, 2, v_share1_916_);
lean_inc_ref(v___f_919_);
v___f_920_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_920_, 0, v___f_919_);
v___f_921_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_921_, 0, v___f_919_);
lean_closure_set(v___f_921_, 1, v_assertShared_917_);
lean_closure_set(v___f_921_, 2, v_a_914_);
lean_closure_set(v___f_921_, 3, v_toBind_915_);
lean_closure_set(v___f_921_, 4, v___f_920_);
lean_closure_set(v___f_921_, 5, v_f_913_);
v___x_922_ = lean_apply_4(v_toBind_915_, lean_box(0), lean_box(0), v_isDebugEnabled_918_, v___f_921_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS(lean_object* v_m_923_, lean_object* v_inst_924_, lean_object* v_inst_925_, lean_object* v_f_926_, lean_object* v_a_927_){
_start:
{
lean_object* v___x_928_; 
v___x_928_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_924_, v_inst_925_, v_f_926_, v_a_927_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__0(lean_object* v_x_929_, lean_object* v_t_930_, lean_object* v_b_931_, uint8_t v_bi_932_, lean_object* v_share1_933_, lean_object* v_____r_934_){
_start:
{
lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_935_ = l_Lean_Expr_lam___override(v_x_929_, v_t_930_, v_b_931_, v_bi_932_);
v___x_936_ = lean_apply_1(v_share1_933_, v___x_935_);
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__0___boxed(lean_object* v_x_937_, lean_object* v_t_938_, lean_object* v_b_939_, lean_object* v_bi_940_, lean_object* v_share1_941_, lean_object* v_____r_942_){
_start:
{
uint8_t v_bi_boxed_943_; lean_object* v_res_944_; 
v_bi_boxed_943_ = lean_unbox(v_bi_940_);
v_res_944_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__0(v_x_937_, v_t_938_, v_b_939_, v_bi_boxed_943_, v_share1_941_, v_____r_942_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__2(lean_object* v_assertShared_945_, lean_object* v_b_946_, lean_object* v_toBind_947_, lean_object* v___f_948_, lean_object* v_____r_949_){
_start:
{
lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_950_ = lean_apply_1(v_assertShared_945_, v_b_946_);
v___x_951_ = lean_apply_4(v_toBind_947_, lean_box(0), lean_box(0), v___x_950_, v___f_948_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1(lean_object* v___f_952_, lean_object* v_assertShared_953_, lean_object* v_b_954_, lean_object* v_toBind_955_, lean_object* v___f_956_, lean_object* v_t_957_, uint8_t v_____do__lift_958_){
_start:
{
if (v_____do__lift_958_ == 0)
{
lean_object* v___x_959_; lean_object* v___x_960_; 
lean_dec_ref(v_t_957_);
lean_dec(v___f_956_);
lean_dec(v_toBind_955_);
lean_dec_ref(v_b_954_);
lean_dec(v_assertShared_953_);
v___x_959_ = lean_box(0);
v___x_960_ = lean_apply_1(v___f_952_, v___x_959_);
return v___x_960_;
}
else
{
lean_object* v___f_961_; lean_object* v___x_962_; lean_object* v___x_963_; 
lean_dec(v___f_952_);
lean_inc(v_toBind_955_);
lean_inc(v_assertShared_953_);
v___f_961_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__2), 5, 4);
lean_closure_set(v___f_961_, 0, v_assertShared_953_);
lean_closure_set(v___f_961_, 1, v_b_954_);
lean_closure_set(v___f_961_, 2, v_toBind_955_);
lean_closure_set(v___f_961_, 3, v___f_956_);
v___x_962_ = lean_apply_1(v_assertShared_953_, v_t_957_);
v___x_963_ = lean_apply_4(v_toBind_955_, lean_box(0), lean_box(0), v___x_962_, v___f_961_);
return v___x_963_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1___boxed(lean_object* v___f_964_, lean_object* v_assertShared_965_, lean_object* v_b_966_, lean_object* v_toBind_967_, lean_object* v___f_968_, lean_object* v_t_969_, lean_object* v_____do__lift_970_){
_start:
{
uint8_t v_____do__lift_75__boxed_971_; lean_object* v_res_972_; 
v_____do__lift_75__boxed_971_ = lean_unbox(v_____do__lift_970_);
v_res_972_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1(v___f_964_, v_assertShared_965_, v_b_966_, v_toBind_967_, v___f_968_, v_t_969_, v_____do__lift_75__boxed_971_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(lean_object* v_inst_973_, lean_object* v_inst_974_, lean_object* v_x_975_, uint8_t v_bi_976_, lean_object* v_t_977_, lean_object* v_b_978_){
_start:
{
lean_object* v_toBind_979_; lean_object* v_share1_980_; lean_object* v_assertShared_981_; lean_object* v_isDebugEnabled_982_; lean_object* v___x_983_; lean_object* v___f_984_; lean_object* v___f_985_; lean_object* v___f_986_; lean_object* v___x_987_; 
v_toBind_979_ = lean_ctor_get(v_inst_974_, 1);
lean_inc_n(v_toBind_979_, 2);
lean_dec_ref(v_inst_974_);
v_share1_980_ = lean_ctor_get(v_inst_973_, 0);
lean_inc(v_share1_980_);
v_assertShared_981_ = lean_ctor_get(v_inst_973_, 1);
lean_inc(v_assertShared_981_);
v_isDebugEnabled_982_ = lean_ctor_get(v_inst_973_, 2);
lean_inc(v_isDebugEnabled_982_);
lean_dec_ref(v_inst_973_);
v___x_983_ = lean_box(v_bi_976_);
lean_inc_ref(v_b_978_);
lean_inc_ref(v_t_977_);
v___f_984_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_984_, 0, v_x_975_);
lean_closure_set(v___f_984_, 1, v_t_977_);
lean_closure_set(v___f_984_, 2, v_b_978_);
lean_closure_set(v___f_984_, 3, v___x_983_);
lean_closure_set(v___f_984_, 4, v_share1_980_);
lean_inc_ref(v___f_984_);
v___f_985_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_985_, 0, v___f_984_);
v___f_986_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_986_, 0, v___f_984_);
lean_closure_set(v___f_986_, 1, v_assertShared_981_);
lean_closure_set(v___f_986_, 2, v_b_978_);
lean_closure_set(v___f_986_, 3, v_toBind_979_);
lean_closure_set(v___f_986_, 4, v___f_985_);
lean_closure_set(v___f_986_, 5, v_t_977_);
v___x_987_ = lean_apply_4(v_toBind_979_, lean_box(0), lean_box(0), v_isDebugEnabled_982_, v___f_986_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___boxed(lean_object* v_inst_988_, lean_object* v_inst_989_, lean_object* v_x_990_, lean_object* v_bi_991_, lean_object* v_t_992_, lean_object* v_b_993_){
_start:
{
uint8_t v_bi_boxed_994_; lean_object* v_res_995_; 
v_bi_boxed_994_ = lean_unbox(v_bi_991_);
v_res_995_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v_inst_988_, v_inst_989_, v_x_990_, v_bi_boxed_994_, v_t_992_, v_b_993_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS(lean_object* v_m_996_, lean_object* v_inst_997_, lean_object* v_inst_998_, lean_object* v_x_999_, uint8_t v_bi_1000_, lean_object* v_t_1001_, lean_object* v_b_1002_){
_start:
{
lean_object* v___x_1003_; 
v___x_1003_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v_inst_997_, v_inst_998_, v_x_999_, v_bi_1000_, v_t_1001_, v_b_1002_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___boxed(lean_object* v_m_1004_, lean_object* v_inst_1005_, lean_object* v_inst_1006_, lean_object* v_x_1007_, lean_object* v_bi_1008_, lean_object* v_t_1009_, lean_object* v_b_1010_){
_start:
{
uint8_t v_bi_boxed_1011_; lean_object* v_res_1012_; 
v_bi_boxed_1011_ = lean_unbox(v_bi_1008_);
v_res_1012_ = l_Lean_Meta_Sym_Internal_mkLambdaS(v_m_1004_, v_inst_1005_, v_inst_1006_, v_x_1007_, v_bi_boxed_1011_, v_t_1009_, v_b_1010_);
return v_res_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___redArg___lam__0(lean_object* v_x_1013_, lean_object* v_t_1014_, lean_object* v_b_1015_, uint8_t v_bi_1016_, lean_object* v_share1_1017_, lean_object* v_____r_1018_){
_start:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1019_ = l_Lean_Expr_forallE___override(v_x_1013_, v_t_1014_, v_b_1015_, v_bi_1016_);
v___x_1020_ = lean_apply_1(v_share1_1017_, v___x_1019_);
return v___x_1020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___redArg___lam__0___boxed(lean_object* v_x_1021_, lean_object* v_t_1022_, lean_object* v_b_1023_, lean_object* v_bi_1024_, lean_object* v_share1_1025_, lean_object* v_____r_1026_){
_start:
{
uint8_t v_bi_boxed_1027_; lean_object* v_res_1028_; 
v_bi_boxed_1027_ = lean_unbox(v_bi_1024_);
v_res_1028_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg___lam__0(v_x_1021_, v_t_1022_, v_b_1023_, v_bi_boxed_1027_, v_share1_1025_, v_____r_1026_);
return v_res_1028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___redArg(lean_object* v_inst_1029_, lean_object* v_inst_1030_, lean_object* v_x_1031_, uint8_t v_bi_1032_, lean_object* v_t_1033_, lean_object* v_b_1034_){
_start:
{
lean_object* v_toBind_1035_; lean_object* v_share1_1036_; lean_object* v_assertShared_1037_; lean_object* v_isDebugEnabled_1038_; lean_object* v___x_1039_; lean_object* v___f_1040_; lean_object* v___f_1041_; lean_object* v___f_1042_; lean_object* v___x_1043_; 
v_toBind_1035_ = lean_ctor_get(v_inst_1030_, 1);
lean_inc_n(v_toBind_1035_, 2);
lean_dec_ref(v_inst_1030_);
v_share1_1036_ = lean_ctor_get(v_inst_1029_, 0);
lean_inc(v_share1_1036_);
v_assertShared_1037_ = lean_ctor_get(v_inst_1029_, 1);
lean_inc(v_assertShared_1037_);
v_isDebugEnabled_1038_ = lean_ctor_get(v_inst_1029_, 2);
lean_inc(v_isDebugEnabled_1038_);
lean_dec_ref(v_inst_1029_);
v___x_1039_ = lean_box(v_bi_1032_);
lean_inc_ref(v_b_1034_);
lean_inc_ref(v_t_1033_);
v___f_1040_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkForallS___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1040_, 0, v_x_1031_);
lean_closure_set(v___f_1040_, 1, v_t_1033_);
lean_closure_set(v___f_1040_, 2, v_b_1034_);
lean_closure_set(v___f_1040_, 3, v___x_1039_);
lean_closure_set(v___f_1040_, 4, v_share1_1036_);
lean_inc_ref(v___f_1040_);
v___f_1041_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1041_, 0, v___f_1040_);
v___f_1042_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_1042_, 0, v___f_1040_);
lean_closure_set(v___f_1042_, 1, v_assertShared_1037_);
lean_closure_set(v___f_1042_, 2, v_b_1034_);
lean_closure_set(v___f_1042_, 3, v_toBind_1035_);
lean_closure_set(v___f_1042_, 4, v___f_1041_);
lean_closure_set(v___f_1042_, 5, v_t_1033_);
v___x_1043_ = lean_apply_4(v_toBind_1035_, lean_box(0), lean_box(0), v_isDebugEnabled_1038_, v___f_1042_);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___redArg___boxed(lean_object* v_inst_1044_, lean_object* v_inst_1045_, lean_object* v_x_1046_, lean_object* v_bi_1047_, lean_object* v_t_1048_, lean_object* v_b_1049_){
_start:
{
uint8_t v_bi_boxed_1050_; lean_object* v_res_1051_; 
v_bi_boxed_1050_ = lean_unbox(v_bi_1047_);
v_res_1051_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v_inst_1044_, v_inst_1045_, v_x_1046_, v_bi_boxed_1050_, v_t_1048_, v_b_1049_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS(lean_object* v_m_1052_, lean_object* v_inst_1053_, lean_object* v_inst_1054_, lean_object* v_x_1055_, uint8_t v_bi_1056_, lean_object* v_t_1057_, lean_object* v_b_1058_){
_start:
{
lean_object* v___x_1059_; 
v___x_1059_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v_inst_1053_, v_inst_1054_, v_x_1055_, v_bi_1056_, v_t_1057_, v_b_1058_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___boxed(lean_object* v_m_1060_, lean_object* v_inst_1061_, lean_object* v_inst_1062_, lean_object* v_x_1063_, lean_object* v_bi_1064_, lean_object* v_t_1065_, lean_object* v_b_1066_){
_start:
{
uint8_t v_bi_boxed_1067_; lean_object* v_res_1068_; 
v_bi_boxed_1067_ = lean_unbox(v_bi_1064_);
v_res_1068_ = l_Lean_Meta_Sym_Internal_mkForallS(v_m_1060_, v_inst_1061_, v_inst_1062_, v_x_1063_, v_bi_boxed_1067_, v_t_1065_, v_b_1066_);
return v_res_1068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__0(lean_object* v_x_1069_, lean_object* v_t_1070_, lean_object* v_v_1071_, lean_object* v_b_1072_, uint8_t v_nondep_1073_, lean_object* v_share1_1074_, lean_object* v_____r_1075_){
_start:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1076_ = l_Lean_Expr_letE___override(v_x_1069_, v_t_1070_, v_v_1071_, v_b_1072_, v_nondep_1073_);
v___x_1077_ = lean_apply_1(v_share1_1074_, v___x_1076_);
return v___x_1077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__0___boxed(lean_object* v_x_1078_, lean_object* v_t_1079_, lean_object* v_v_1080_, lean_object* v_b_1081_, lean_object* v_nondep_1082_, lean_object* v_share1_1083_, lean_object* v_____r_1084_){
_start:
{
uint8_t v_nondep_boxed_1085_; lean_object* v_res_1086_; 
v_nondep_boxed_1085_ = lean_unbox(v_nondep_1082_);
v_res_1086_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__0(v_x_1078_, v_t_1079_, v_v_1080_, v_b_1081_, v_nondep_boxed_1085_, v_share1_1083_, v_____r_1084_);
return v_res_1086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__3(lean_object* v_assertShared_1087_, lean_object* v_v_1088_, lean_object* v_toBind_1089_, lean_object* v___f_1090_, lean_object* v_____r_1091_){
_start:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1092_ = lean_apply_1(v_assertShared_1087_, v_v_1088_);
v___x_1093_ = lean_apply_4(v_toBind_1089_, lean_box(0), lean_box(0), v___x_1092_, v___f_1090_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1(lean_object* v___f_1094_, lean_object* v_assertShared_1095_, lean_object* v_b_1096_, lean_object* v_toBind_1097_, lean_object* v___f_1098_, lean_object* v_v_1099_, lean_object* v_t_1100_, uint8_t v_____do__lift_1101_){
_start:
{
if (v_____do__lift_1101_ == 0)
{
lean_object* v___x_1102_; lean_object* v___x_1103_; 
lean_dec_ref(v_t_1100_);
lean_dec_ref(v_v_1099_);
lean_dec(v___f_1098_);
lean_dec(v_toBind_1097_);
lean_dec_ref(v_b_1096_);
lean_dec(v_assertShared_1095_);
v___x_1102_ = lean_box(0);
v___x_1103_ = lean_apply_1(v___f_1094_, v___x_1102_);
return v___x_1103_;
}
else
{
lean_object* v___f_1104_; lean_object* v___f_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; 
lean_dec(v___f_1094_);
lean_inc_n(v_toBind_1097_, 2);
lean_inc_n(v_assertShared_1095_, 2);
v___f_1104_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__2), 5, 4);
lean_closure_set(v___f_1104_, 0, v_assertShared_1095_);
lean_closure_set(v___f_1104_, 1, v_b_1096_);
lean_closure_set(v___f_1104_, 2, v_toBind_1097_);
lean_closure_set(v___f_1104_, 3, v___f_1098_);
v___f_1105_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__3), 5, 4);
lean_closure_set(v___f_1105_, 0, v_assertShared_1095_);
lean_closure_set(v___f_1105_, 1, v_v_1099_);
lean_closure_set(v___f_1105_, 2, v_toBind_1097_);
lean_closure_set(v___f_1105_, 3, v___f_1104_);
v___x_1106_ = lean_apply_1(v_assertShared_1095_, v_t_1100_);
v___x_1107_ = lean_apply_4(v_toBind_1097_, lean_box(0), lean_box(0), v___x_1106_, v___f_1105_);
return v___x_1107_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1___boxed(lean_object* v___f_1108_, lean_object* v_assertShared_1109_, lean_object* v_b_1110_, lean_object* v_toBind_1111_, lean_object* v___f_1112_, lean_object* v_v_1113_, lean_object* v_t_1114_, lean_object* v_____do__lift_1115_){
_start:
{
uint8_t v_____do__lift_84__boxed_1116_; lean_object* v_res_1117_; 
v_____do__lift_84__boxed_1116_ = lean_unbox(v_____do__lift_1115_);
v_res_1117_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1(v___f_1108_, v_assertShared_1109_, v_b_1110_, v_toBind_1111_, v___f_1112_, v_v_1113_, v_t_1114_, v_____do__lift_84__boxed_1116_);
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg(lean_object* v_inst_1118_, lean_object* v_inst_1119_, lean_object* v_x_1120_, lean_object* v_t_1121_, lean_object* v_v_1122_, lean_object* v_b_1123_, uint8_t v_nondep_1124_){
_start:
{
lean_object* v_toBind_1125_; lean_object* v_share1_1126_; lean_object* v_assertShared_1127_; lean_object* v_isDebugEnabled_1128_; lean_object* v___x_1129_; lean_object* v___f_1130_; lean_object* v___f_1131_; lean_object* v___f_1132_; lean_object* v___x_1133_; 
v_toBind_1125_ = lean_ctor_get(v_inst_1119_, 1);
lean_inc_n(v_toBind_1125_, 2);
lean_dec_ref(v_inst_1119_);
v_share1_1126_ = lean_ctor_get(v_inst_1118_, 0);
lean_inc(v_share1_1126_);
v_assertShared_1127_ = lean_ctor_get(v_inst_1118_, 1);
lean_inc(v_assertShared_1127_);
v_isDebugEnabled_1128_ = lean_ctor_get(v_inst_1118_, 2);
lean_inc(v_isDebugEnabled_1128_);
lean_dec_ref(v_inst_1118_);
v___x_1129_ = lean_box(v_nondep_1124_);
lean_inc_ref(v_b_1123_);
lean_inc_ref(v_v_1122_);
lean_inc_ref(v_t_1121_);
v___f_1130_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_1130_, 0, v_x_1120_);
lean_closure_set(v___f_1130_, 1, v_t_1121_);
lean_closure_set(v___f_1130_, 2, v_v_1122_);
lean_closure_set(v___f_1130_, 3, v_b_1123_);
lean_closure_set(v___f_1130_, 4, v___x_1129_);
lean_closure_set(v___f_1130_, 5, v_share1_1126_);
lean_inc_ref(v___f_1130_);
v___f_1131_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1131_, 0, v___f_1130_);
v___f_1132_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_1132_, 0, v___f_1130_);
lean_closure_set(v___f_1132_, 1, v_assertShared_1127_);
lean_closure_set(v___f_1132_, 2, v_b_1123_);
lean_closure_set(v___f_1132_, 3, v_toBind_1125_);
lean_closure_set(v___f_1132_, 4, v___f_1131_);
lean_closure_set(v___f_1132_, 5, v_v_1122_);
lean_closure_set(v___f_1132_, 6, v_t_1121_);
v___x_1133_ = lean_apply_4(v_toBind_1125_, lean_box(0), lean_box(0), v_isDebugEnabled_1128_, v___f_1132_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___boxed(lean_object* v_inst_1134_, lean_object* v_inst_1135_, lean_object* v_x_1136_, lean_object* v_t_1137_, lean_object* v_v_1138_, lean_object* v_b_1139_, lean_object* v_nondep_1140_){
_start:
{
uint8_t v_nondep_boxed_1141_; lean_object* v_res_1142_; 
v_nondep_boxed_1141_ = lean_unbox(v_nondep_1140_);
v_res_1142_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1134_, v_inst_1135_, v_x_1136_, v_t_1137_, v_v_1138_, v_b_1139_, v_nondep_boxed_1141_);
return v_res_1142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS(lean_object* v_m_1143_, lean_object* v_inst_1144_, lean_object* v_inst_1145_, lean_object* v_x_1146_, lean_object* v_t_1147_, lean_object* v_v_1148_, lean_object* v_b_1149_, uint8_t v_nondep_1150_){
_start:
{
lean_object* v___x_1151_; 
v___x_1151_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1144_, v_inst_1145_, v_x_1146_, v_t_1147_, v_v_1148_, v_b_1149_, v_nondep_1150_);
return v___x_1151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___boxed(lean_object* v_m_1152_, lean_object* v_inst_1153_, lean_object* v_inst_1154_, lean_object* v_x_1155_, lean_object* v_t_1156_, lean_object* v_v_1157_, lean_object* v_b_1158_, lean_object* v_nondep_1159_){
_start:
{
uint8_t v_nondep_boxed_1160_; lean_object* v_res_1161_; 
v_nondep_boxed_1160_ = lean_unbox(v_nondep_1159_);
v_res_1161_ = l_Lean_Meta_Sym_Internal_mkLetS(v_m_1152_, v_inst_1153_, v_inst_1154_, v_x_1155_, v_t_1156_, v_v_1157_, v_b_1158_, v_nondep_boxed_1160_);
return v_res_1161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkHaveS___redArg___lam__0(lean_object* v_x_1162_, lean_object* v_t_1163_, lean_object* v_v_1164_, lean_object* v_b_1165_, lean_object* v_share1_1166_, lean_object* v_____r_1167_){
_start:
{
uint8_t v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; 
v___x_1168_ = 1;
v___x_1169_ = l_Lean_Expr_letE___override(v_x_1162_, v_t_1163_, v_v_1164_, v_b_1165_, v___x_1168_);
v___x_1170_ = lean_apply_1(v_share1_1166_, v___x_1169_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkHaveS___redArg(lean_object* v_inst_1171_, lean_object* v_inst_1172_, lean_object* v_x_1173_, lean_object* v_t_1174_, lean_object* v_v_1175_, lean_object* v_b_1176_){
_start:
{
lean_object* v_toBind_1177_; lean_object* v_share1_1178_; lean_object* v_assertShared_1179_; lean_object* v_isDebugEnabled_1180_; lean_object* v___f_1181_; lean_object* v___f_1182_; lean_object* v___f_1183_; lean_object* v___x_1184_; 
v_toBind_1177_ = lean_ctor_get(v_inst_1172_, 1);
lean_inc_n(v_toBind_1177_, 2);
lean_dec_ref(v_inst_1172_);
v_share1_1178_ = lean_ctor_get(v_inst_1171_, 0);
lean_inc(v_share1_1178_);
v_assertShared_1179_ = lean_ctor_get(v_inst_1171_, 1);
lean_inc(v_assertShared_1179_);
v_isDebugEnabled_1180_ = lean_ctor_get(v_inst_1171_, 2);
lean_inc(v_isDebugEnabled_1180_);
lean_dec_ref(v_inst_1171_);
lean_inc_ref(v_b_1176_);
lean_inc_ref(v_v_1175_);
lean_inc_ref(v_t_1174_);
v___f_1181_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkHaveS___redArg___lam__0), 6, 5);
lean_closure_set(v___f_1181_, 0, v_x_1173_);
lean_closure_set(v___f_1181_, 1, v_t_1174_);
lean_closure_set(v___f_1181_, 2, v_v_1175_);
lean_closure_set(v___f_1181_, 3, v_b_1176_);
lean_closure_set(v___f_1181_, 4, v_share1_1178_);
lean_inc_ref(v___f_1181_);
v___f_1182_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1182_, 0, v___f_1181_);
v___f_1183_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_1183_, 0, v___f_1181_);
lean_closure_set(v___f_1183_, 1, v_assertShared_1179_);
lean_closure_set(v___f_1183_, 2, v_b_1176_);
lean_closure_set(v___f_1183_, 3, v_toBind_1177_);
lean_closure_set(v___f_1183_, 4, v___f_1182_);
lean_closure_set(v___f_1183_, 5, v_v_1175_);
lean_closure_set(v___f_1183_, 6, v_t_1174_);
v___x_1184_ = lean_apply_4(v_toBind_1177_, lean_box(0), lean_box(0), v_isDebugEnabled_1180_, v___f_1183_);
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkHaveS(lean_object* v_m_1185_, lean_object* v_inst_1186_, lean_object* v_inst_1187_, lean_object* v_x_1188_, lean_object* v_t_1189_, lean_object* v_v_1190_, lean_object* v_b_1191_){
_start:
{
lean_object* v___x_1192_; 
v___x_1192_ = l_Lean_Meta_Sym_Internal_mkHaveS___redArg(v_inst_1186_, v_inst_1187_, v_x_1188_, v_t_1189_, v_v_1190_, v_b_1191_);
return v___x_1192_;
}
}
static lean_object* _init_l_Lean_Expr_updateAppS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1195_ = ((lean_object*)(l_Lean_Expr_updateAppS_x21___redArg___closed__1));
v___x_1196_ = lean_unsigned_to_nat(25u);
v___x_1197_ = lean_unsigned_to_nat(148u);
v___x_1198_ = ((lean_object*)(l_Lean_Expr_updateAppS_x21___redArg___closed__0));
v___x_1199_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1200_ = l_mkPanicMessageWithDecl(v___x_1199_, v___x_1198_, v___x_1197_, v___x_1196_, v___x_1195_);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateAppS_x21___redArg(lean_object* v_inst_1201_, lean_object* v_inst_1202_, lean_object* v_e_1203_, lean_object* v_newFn_1204_, lean_object* v_newArg_1205_){
_start:
{
if (lean_obj_tag(v_e_1203_) == 5)
{
lean_object* v_toApplicative_1206_; lean_object* v_toPure_1207_; lean_object* v_fn_1208_; lean_object* v_arg_1209_; size_t v___x_1210_; size_t v___x_1211_; uint8_t v___x_1212_; 
v_toApplicative_1206_ = lean_ctor_get(v_inst_1202_, 0);
v_toPure_1207_ = lean_ctor_get(v_toApplicative_1206_, 1);
v_fn_1208_ = lean_ctor_get(v_e_1203_, 0);
v_arg_1209_ = lean_ctor_get(v_e_1203_, 1);
v___x_1210_ = lean_ptr_addr(v_fn_1208_);
v___x_1211_ = lean_ptr_addr(v_newFn_1204_);
v___x_1212_ = lean_usize_dec_eq(v___x_1210_, v___x_1211_);
if (v___x_1212_ == 0)
{
lean_object* v___x_1213_; 
lean_dec_ref_known(v_e_1203_, 2);
v___x_1213_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1201_, v_inst_1202_, v_newFn_1204_, v_newArg_1205_);
return v___x_1213_;
}
else
{
size_t v___x_1214_; size_t v___x_1215_; uint8_t v___x_1216_; 
v___x_1214_ = lean_ptr_addr(v_arg_1209_);
v___x_1215_ = lean_ptr_addr(v_newArg_1205_);
v___x_1216_ = lean_usize_dec_eq(v___x_1214_, v___x_1215_);
if (v___x_1216_ == 0)
{
lean_object* v___x_1217_; 
lean_dec_ref_known(v_e_1203_, 2);
v___x_1217_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1201_, v_inst_1202_, v_newFn_1204_, v_newArg_1205_);
return v___x_1217_;
}
else
{
lean_object* v___x_1218_; 
lean_inc(v_toPure_1207_);
lean_dec_ref(v_newArg_1205_);
lean_dec_ref(v_newFn_1204_);
lean_dec_ref(v_inst_1202_);
lean_dec_ref(v_inst_1201_);
v___x_1218_ = lean_apply_2(v_toPure_1207_, lean_box(0), v_e_1203_);
return v___x_1218_;
}
}
}
else
{
lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; 
lean_dec_ref(v_newArg_1205_);
lean_dec_ref(v_newFn_1204_);
lean_dec_ref(v_e_1203_);
lean_dec_ref(v_inst_1201_);
v___x_1219_ = l_Lean_instInhabitedExpr;
v___x_1220_ = l_instInhabitedOfMonad___redArg(v_inst_1202_, v___x_1219_);
v___x_1221_ = lean_obj_once(&l_Lean_Expr_updateAppS_x21___redArg___closed__2, &l_Lean_Expr_updateAppS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateAppS_x21___redArg___closed__2);
v___x_1222_ = l_panic___redArg(v___x_1220_, v___x_1221_);
lean_dec(v___x_1220_);
return v___x_1222_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateAppS_x21(lean_object* v_m_1223_, lean_object* v_inst_1224_, lean_object* v_inst_1225_, lean_object* v_e_1226_, lean_object* v_newFn_1227_, lean_object* v_newArg_1228_){
_start:
{
if (lean_obj_tag(v_e_1226_) == 5)
{
lean_object* v_toApplicative_1229_; lean_object* v_toPure_1230_; lean_object* v_fn_1231_; lean_object* v_arg_1232_; size_t v___x_1233_; size_t v___x_1234_; uint8_t v___x_1235_; 
v_toApplicative_1229_ = lean_ctor_get(v_inst_1225_, 0);
v_toPure_1230_ = lean_ctor_get(v_toApplicative_1229_, 1);
v_fn_1231_ = lean_ctor_get(v_e_1226_, 0);
v_arg_1232_ = lean_ctor_get(v_e_1226_, 1);
v___x_1233_ = lean_ptr_addr(v_fn_1231_);
v___x_1234_ = lean_ptr_addr(v_newFn_1227_);
v___x_1235_ = lean_usize_dec_eq(v___x_1233_, v___x_1234_);
if (v___x_1235_ == 0)
{
lean_object* v___x_1236_; 
lean_dec_ref_known(v_e_1226_, 2);
v___x_1236_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1224_, v_inst_1225_, v_newFn_1227_, v_newArg_1228_);
return v___x_1236_;
}
else
{
size_t v___x_1237_; size_t v___x_1238_; uint8_t v___x_1239_; 
v___x_1237_ = lean_ptr_addr(v_arg_1232_);
v___x_1238_ = lean_ptr_addr(v_newArg_1228_);
v___x_1239_ = lean_usize_dec_eq(v___x_1237_, v___x_1238_);
if (v___x_1239_ == 0)
{
lean_object* v___x_1240_; 
lean_dec_ref_known(v_e_1226_, 2);
v___x_1240_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1224_, v_inst_1225_, v_newFn_1227_, v_newArg_1228_);
return v___x_1240_;
}
else
{
lean_object* v___x_1241_; 
lean_inc(v_toPure_1230_);
lean_dec_ref(v_newArg_1228_);
lean_dec_ref(v_newFn_1227_);
lean_dec_ref(v_inst_1225_);
lean_dec_ref(v_inst_1224_);
v___x_1241_ = lean_apply_2(v_toPure_1230_, lean_box(0), v_e_1226_);
return v___x_1241_;
}
}
}
else
{
lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; 
lean_dec_ref(v_newArg_1228_);
lean_dec_ref(v_newFn_1227_);
lean_dec_ref(v_e_1226_);
lean_dec_ref(v_inst_1224_);
v___x_1242_ = l_Lean_instInhabitedExpr;
v___x_1243_ = l_instInhabitedOfMonad___redArg(v_inst_1225_, v___x_1242_);
v___x_1244_ = lean_obj_once(&l_Lean_Expr_updateAppS_x21___redArg___closed__2, &l_Lean_Expr_updateAppS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateAppS_x21___redArg___closed__2);
v___x_1245_ = l_panic___redArg(v___x_1243_, v___x_1244_);
lean_dec(v___x_1243_);
return v___x_1245_;
}
}
}
static lean_object* _init_l_Lean_Expr_updateMDataS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1248_ = ((lean_object*)(l_Lean_Expr_updateMDataS_x21___redArg___closed__1));
v___x_1249_ = lean_unsigned_to_nat(24u);
v___x_1250_ = lean_unsigned_to_nat(152u);
v___x_1251_ = ((lean_object*)(l_Lean_Expr_updateMDataS_x21___redArg___closed__0));
v___x_1252_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1253_ = l_mkPanicMessageWithDecl(v___x_1252_, v___x_1251_, v___x_1250_, v___x_1249_, v___x_1248_);
return v___x_1253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateMDataS_x21___redArg(lean_object* v_inst_1254_, lean_object* v_inst_1255_, lean_object* v_e_1256_, lean_object* v_newExpr_1257_){
_start:
{
if (lean_obj_tag(v_e_1256_) == 10)
{
lean_object* v_toApplicative_1258_; lean_object* v_toPure_1259_; lean_object* v_data_1260_; lean_object* v_expr_1261_; size_t v___x_1262_; size_t v___x_1263_; uint8_t v___x_1264_; 
v_toApplicative_1258_ = lean_ctor_get(v_inst_1255_, 0);
v_toPure_1259_ = lean_ctor_get(v_toApplicative_1258_, 1);
v_data_1260_ = lean_ctor_get(v_e_1256_, 0);
v_expr_1261_ = lean_ctor_get(v_e_1256_, 1);
v___x_1262_ = lean_ptr_addr(v_expr_1261_);
v___x_1263_ = lean_ptr_addr(v_newExpr_1257_);
v___x_1264_ = lean_usize_dec_eq(v___x_1262_, v___x_1263_);
if (v___x_1264_ == 0)
{
lean_object* v___x_1265_; 
lean_inc(v_data_1260_);
lean_dec_ref_known(v_e_1256_, 2);
v___x_1265_ = l_Lean_Meta_Sym_Internal_mkMDataS___redArg(v_inst_1254_, v_inst_1255_, v_data_1260_, v_newExpr_1257_);
return v___x_1265_;
}
else
{
lean_object* v___x_1266_; 
lean_inc(v_toPure_1259_);
lean_dec_ref(v_newExpr_1257_);
lean_dec_ref(v_inst_1255_);
lean_dec_ref(v_inst_1254_);
v___x_1266_ = lean_apply_2(v_toPure_1259_, lean_box(0), v_e_1256_);
return v___x_1266_;
}
}
else
{
lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; 
lean_dec_ref(v_newExpr_1257_);
lean_dec_ref(v_e_1256_);
lean_dec_ref(v_inst_1254_);
v___x_1267_ = l_Lean_instInhabitedExpr;
v___x_1268_ = l_instInhabitedOfMonad___redArg(v_inst_1255_, v___x_1267_);
v___x_1269_ = lean_obj_once(&l_Lean_Expr_updateMDataS_x21___redArg___closed__2, &l_Lean_Expr_updateMDataS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateMDataS_x21___redArg___closed__2);
v___x_1270_ = l_panic___redArg(v___x_1268_, v___x_1269_);
lean_dec(v___x_1268_);
return v___x_1270_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateMDataS_x21(lean_object* v_m_1271_, lean_object* v_inst_1272_, lean_object* v_inst_1273_, lean_object* v_e_1274_, lean_object* v_newExpr_1275_){
_start:
{
if (lean_obj_tag(v_e_1274_) == 10)
{
lean_object* v_toApplicative_1276_; lean_object* v_toPure_1277_; lean_object* v_data_1278_; lean_object* v_expr_1279_; size_t v___x_1280_; size_t v___x_1281_; uint8_t v___x_1282_; 
v_toApplicative_1276_ = lean_ctor_get(v_inst_1273_, 0);
v_toPure_1277_ = lean_ctor_get(v_toApplicative_1276_, 1);
v_data_1278_ = lean_ctor_get(v_e_1274_, 0);
v_expr_1279_ = lean_ctor_get(v_e_1274_, 1);
v___x_1280_ = lean_ptr_addr(v_expr_1279_);
v___x_1281_ = lean_ptr_addr(v_newExpr_1275_);
v___x_1282_ = lean_usize_dec_eq(v___x_1280_, v___x_1281_);
if (v___x_1282_ == 0)
{
lean_object* v___x_1283_; 
lean_inc(v_data_1278_);
lean_dec_ref_known(v_e_1274_, 2);
v___x_1283_ = l_Lean_Meta_Sym_Internal_mkMDataS___redArg(v_inst_1272_, v_inst_1273_, v_data_1278_, v_newExpr_1275_);
return v___x_1283_;
}
else
{
lean_object* v___x_1284_; 
lean_inc(v_toPure_1277_);
lean_dec_ref(v_newExpr_1275_);
lean_dec_ref(v_inst_1273_);
lean_dec_ref(v_inst_1272_);
v___x_1284_ = lean_apply_2(v_toPure_1277_, lean_box(0), v_e_1274_);
return v___x_1284_;
}
}
else
{
lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; 
lean_dec_ref(v_newExpr_1275_);
lean_dec_ref(v_e_1274_);
lean_dec_ref(v_inst_1272_);
v___x_1285_ = l_Lean_instInhabitedExpr;
v___x_1286_ = l_instInhabitedOfMonad___redArg(v_inst_1273_, v___x_1285_);
v___x_1287_ = lean_obj_once(&l_Lean_Expr_updateMDataS_x21___redArg___closed__2, &l_Lean_Expr_updateMDataS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateMDataS_x21___redArg___closed__2);
v___x_1288_ = l_panic___redArg(v___x_1286_, v___x_1287_);
lean_dec(v___x_1286_);
return v___x_1288_;
}
}
}
static lean_object* _init_l_Lean_Expr_updateProjS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; 
v___x_1291_ = ((lean_object*)(l_Lean_Expr_updateProjS_x21___redArg___closed__1));
v___x_1292_ = lean_unsigned_to_nat(25u);
v___x_1293_ = lean_unsigned_to_nat(156u);
v___x_1294_ = ((lean_object*)(l_Lean_Expr_updateProjS_x21___redArg___closed__0));
v___x_1295_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1296_ = l_mkPanicMessageWithDecl(v___x_1295_, v___x_1294_, v___x_1293_, v___x_1292_, v___x_1291_);
return v___x_1296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateProjS_x21___redArg(lean_object* v_inst_1297_, lean_object* v_inst_1298_, lean_object* v_e_1299_, lean_object* v_newExpr_1300_){
_start:
{
if (lean_obj_tag(v_e_1299_) == 11)
{
lean_object* v_toApplicative_1301_; lean_object* v_toPure_1302_; lean_object* v_typeName_1303_; lean_object* v_idx_1304_; lean_object* v_struct_1305_; size_t v___x_1306_; size_t v___x_1307_; uint8_t v___x_1308_; 
v_toApplicative_1301_ = lean_ctor_get(v_inst_1298_, 0);
v_toPure_1302_ = lean_ctor_get(v_toApplicative_1301_, 1);
v_typeName_1303_ = lean_ctor_get(v_e_1299_, 0);
v_idx_1304_ = lean_ctor_get(v_e_1299_, 1);
v_struct_1305_ = lean_ctor_get(v_e_1299_, 2);
v___x_1306_ = lean_ptr_addr(v_struct_1305_);
v___x_1307_ = lean_ptr_addr(v_newExpr_1300_);
v___x_1308_ = lean_usize_dec_eq(v___x_1306_, v___x_1307_);
if (v___x_1308_ == 0)
{
lean_object* v___x_1309_; 
lean_inc(v_idx_1304_);
lean_inc(v_typeName_1303_);
lean_dec_ref_known(v_e_1299_, 3);
v___x_1309_ = l_Lean_Meta_Sym_Internal_mkProjS___redArg(v_inst_1297_, v_inst_1298_, v_typeName_1303_, v_idx_1304_, v_newExpr_1300_);
return v___x_1309_;
}
else
{
lean_object* v___x_1310_; 
lean_inc(v_toPure_1302_);
lean_dec_ref(v_newExpr_1300_);
lean_dec_ref(v_inst_1298_);
lean_dec_ref(v_inst_1297_);
v___x_1310_ = lean_apply_2(v_toPure_1302_, lean_box(0), v_e_1299_);
return v___x_1310_;
}
}
else
{
lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; 
lean_dec_ref(v_newExpr_1300_);
lean_dec_ref(v_e_1299_);
lean_dec_ref(v_inst_1297_);
v___x_1311_ = l_Lean_instInhabitedExpr;
v___x_1312_ = l_instInhabitedOfMonad___redArg(v_inst_1298_, v___x_1311_);
v___x_1313_ = lean_obj_once(&l_Lean_Expr_updateProjS_x21___redArg___closed__2, &l_Lean_Expr_updateProjS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateProjS_x21___redArg___closed__2);
v___x_1314_ = l_panic___redArg(v___x_1312_, v___x_1313_);
lean_dec(v___x_1312_);
return v___x_1314_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateProjS_x21(lean_object* v_m_1315_, lean_object* v_inst_1316_, lean_object* v_inst_1317_, lean_object* v_e_1318_, lean_object* v_newExpr_1319_){
_start:
{
if (lean_obj_tag(v_e_1318_) == 11)
{
lean_object* v_toApplicative_1320_; lean_object* v_toPure_1321_; lean_object* v_typeName_1322_; lean_object* v_idx_1323_; lean_object* v_struct_1324_; size_t v___x_1325_; size_t v___x_1326_; uint8_t v___x_1327_; 
v_toApplicative_1320_ = lean_ctor_get(v_inst_1317_, 0);
v_toPure_1321_ = lean_ctor_get(v_toApplicative_1320_, 1);
v_typeName_1322_ = lean_ctor_get(v_e_1318_, 0);
v_idx_1323_ = lean_ctor_get(v_e_1318_, 1);
v_struct_1324_ = lean_ctor_get(v_e_1318_, 2);
v___x_1325_ = lean_ptr_addr(v_struct_1324_);
v___x_1326_ = lean_ptr_addr(v_newExpr_1319_);
v___x_1327_ = lean_usize_dec_eq(v___x_1325_, v___x_1326_);
if (v___x_1327_ == 0)
{
lean_object* v___x_1328_; 
lean_inc(v_idx_1323_);
lean_inc(v_typeName_1322_);
lean_dec_ref_known(v_e_1318_, 3);
v___x_1328_ = l_Lean_Meta_Sym_Internal_mkProjS___redArg(v_inst_1316_, v_inst_1317_, v_typeName_1322_, v_idx_1323_, v_newExpr_1319_);
return v___x_1328_;
}
else
{
lean_object* v___x_1329_; 
lean_inc(v_toPure_1321_);
lean_dec_ref(v_newExpr_1319_);
lean_dec_ref(v_inst_1317_);
lean_dec_ref(v_inst_1316_);
v___x_1329_ = lean_apply_2(v_toPure_1321_, lean_box(0), v_e_1318_);
return v___x_1329_;
}
}
else
{
lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; 
lean_dec_ref(v_newExpr_1319_);
lean_dec_ref(v_e_1318_);
lean_dec_ref(v_inst_1316_);
v___x_1330_ = l_Lean_instInhabitedExpr;
v___x_1331_ = l_instInhabitedOfMonad___redArg(v_inst_1317_, v___x_1330_);
v___x_1332_ = lean_obj_once(&l_Lean_Expr_updateProjS_x21___redArg___closed__2, &l_Lean_Expr_updateProjS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateProjS_x21___redArg___closed__2);
v___x_1333_ = l_panic___redArg(v___x_1331_, v___x_1332_);
lean_dec(v___x_1331_);
return v___x_1333_;
}
}
}
static lean_object* _init_l_Lean_Expr_updateForallS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; 
v___x_1336_ = ((lean_object*)(l_Lean_Expr_updateForallS_x21___redArg___closed__1));
v___x_1337_ = lean_unsigned_to_nat(31u);
v___x_1338_ = lean_unsigned_to_nat(160u);
v___x_1339_ = ((lean_object*)(l_Lean_Expr_updateForallS_x21___redArg___closed__0));
v___x_1340_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1341_ = l_mkPanicMessageWithDecl(v___x_1340_, v___x_1339_, v___x_1338_, v___x_1337_, v___x_1336_);
return v___x_1341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallS_x21___redArg(lean_object* v_inst_1342_, lean_object* v_inst_1343_, lean_object* v_e_1344_, lean_object* v_newDomain_1345_, lean_object* v_newBody_1346_){
_start:
{
if (lean_obj_tag(v_e_1344_) == 7)
{
lean_object* v_toApplicative_1347_; lean_object* v_toPure_1348_; lean_object* v_binderName_1349_; lean_object* v_binderType_1350_; lean_object* v_body_1351_; uint8_t v_binderInfo_1352_; size_t v___x_1353_; size_t v___x_1354_; uint8_t v___x_1355_; 
v_toApplicative_1347_ = lean_ctor_get(v_inst_1343_, 0);
v_toPure_1348_ = lean_ctor_get(v_toApplicative_1347_, 1);
v_binderName_1349_ = lean_ctor_get(v_e_1344_, 0);
v_binderType_1350_ = lean_ctor_get(v_e_1344_, 1);
v_body_1351_ = lean_ctor_get(v_e_1344_, 2);
v_binderInfo_1352_ = lean_ctor_get_uint8(v_e_1344_, sizeof(void*)*3 + 8);
v___x_1353_ = lean_ptr_addr(v_binderType_1350_);
v___x_1354_ = lean_ptr_addr(v_newDomain_1345_);
v___x_1355_ = lean_usize_dec_eq(v___x_1353_, v___x_1354_);
if (v___x_1355_ == 0)
{
lean_object* v___x_1356_; 
lean_inc(v_binderName_1349_);
lean_dec_ref_known(v_e_1344_, 3);
v___x_1356_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v_inst_1342_, v_inst_1343_, v_binderName_1349_, v_binderInfo_1352_, v_newDomain_1345_, v_newBody_1346_);
return v___x_1356_;
}
else
{
size_t v___x_1357_; size_t v___x_1358_; uint8_t v___x_1359_; 
v___x_1357_ = lean_ptr_addr(v_body_1351_);
v___x_1358_ = lean_ptr_addr(v_newBody_1346_);
v___x_1359_ = lean_usize_dec_eq(v___x_1357_, v___x_1358_);
if (v___x_1359_ == 0)
{
lean_object* v___x_1360_; 
lean_inc(v_binderName_1349_);
lean_dec_ref_known(v_e_1344_, 3);
v___x_1360_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v_inst_1342_, v_inst_1343_, v_binderName_1349_, v_binderInfo_1352_, v_newDomain_1345_, v_newBody_1346_);
return v___x_1360_;
}
else
{
lean_object* v___x_1361_; 
lean_inc(v_toPure_1348_);
lean_dec_ref(v_newBody_1346_);
lean_dec_ref(v_newDomain_1345_);
lean_dec_ref(v_inst_1343_);
lean_dec_ref(v_inst_1342_);
v___x_1361_ = lean_apply_2(v_toPure_1348_, lean_box(0), v_e_1344_);
return v___x_1361_;
}
}
}
else
{
lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; 
lean_dec_ref(v_newBody_1346_);
lean_dec_ref(v_newDomain_1345_);
lean_dec_ref(v_e_1344_);
lean_dec_ref(v_inst_1342_);
v___x_1362_ = l_Lean_instInhabitedExpr;
v___x_1363_ = l_instInhabitedOfMonad___redArg(v_inst_1343_, v___x_1362_);
v___x_1364_ = lean_obj_once(&l_Lean_Expr_updateForallS_x21___redArg___closed__2, &l_Lean_Expr_updateForallS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateForallS_x21___redArg___closed__2);
v___x_1365_ = l_panic___redArg(v___x_1363_, v___x_1364_);
lean_dec(v___x_1363_);
return v___x_1365_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallS_x21(lean_object* v_m_1366_, lean_object* v_inst_1367_, lean_object* v_inst_1368_, lean_object* v_e_1369_, lean_object* v_newDomain_1370_, lean_object* v_newBody_1371_){
_start:
{
if (lean_obj_tag(v_e_1369_) == 7)
{
lean_object* v_toApplicative_1372_; lean_object* v_toPure_1373_; lean_object* v_binderName_1374_; lean_object* v_binderType_1375_; lean_object* v_body_1376_; uint8_t v_binderInfo_1377_; size_t v___x_1378_; size_t v___x_1379_; uint8_t v___x_1380_; 
v_toApplicative_1372_ = lean_ctor_get(v_inst_1368_, 0);
v_toPure_1373_ = lean_ctor_get(v_toApplicative_1372_, 1);
v_binderName_1374_ = lean_ctor_get(v_e_1369_, 0);
v_binderType_1375_ = lean_ctor_get(v_e_1369_, 1);
v_body_1376_ = lean_ctor_get(v_e_1369_, 2);
v_binderInfo_1377_ = lean_ctor_get_uint8(v_e_1369_, sizeof(void*)*3 + 8);
v___x_1378_ = lean_ptr_addr(v_binderType_1375_);
v___x_1379_ = lean_ptr_addr(v_newDomain_1370_);
v___x_1380_ = lean_usize_dec_eq(v___x_1378_, v___x_1379_);
if (v___x_1380_ == 0)
{
lean_object* v___x_1381_; 
lean_inc(v_binderName_1374_);
lean_dec_ref_known(v_e_1369_, 3);
v___x_1381_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v_inst_1367_, v_inst_1368_, v_binderName_1374_, v_binderInfo_1377_, v_newDomain_1370_, v_newBody_1371_);
return v___x_1381_;
}
else
{
size_t v___x_1382_; size_t v___x_1383_; uint8_t v___x_1384_; 
v___x_1382_ = lean_ptr_addr(v_body_1376_);
v___x_1383_ = lean_ptr_addr(v_newBody_1371_);
v___x_1384_ = lean_usize_dec_eq(v___x_1382_, v___x_1383_);
if (v___x_1384_ == 0)
{
lean_object* v___x_1385_; 
lean_inc(v_binderName_1374_);
lean_dec_ref_known(v_e_1369_, 3);
v___x_1385_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v_inst_1367_, v_inst_1368_, v_binderName_1374_, v_binderInfo_1377_, v_newDomain_1370_, v_newBody_1371_);
return v___x_1385_;
}
else
{
lean_object* v___x_1386_; 
lean_inc(v_toPure_1373_);
lean_dec_ref(v_newBody_1371_);
lean_dec_ref(v_newDomain_1370_);
lean_dec_ref(v_inst_1368_);
lean_dec_ref(v_inst_1367_);
v___x_1386_ = lean_apply_2(v_toPure_1373_, lean_box(0), v_e_1369_);
return v___x_1386_;
}
}
}
else
{
lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; 
lean_dec_ref(v_newBody_1371_);
lean_dec_ref(v_newDomain_1370_);
lean_dec_ref(v_e_1369_);
lean_dec_ref(v_inst_1367_);
v___x_1387_ = l_Lean_instInhabitedExpr;
v___x_1388_ = l_instInhabitedOfMonad___redArg(v_inst_1368_, v___x_1387_);
v___x_1389_ = lean_obj_once(&l_Lean_Expr_updateForallS_x21___redArg___closed__2, &l_Lean_Expr_updateForallS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateForallS_x21___redArg___closed__2);
v___x_1390_ = l_panic___redArg(v___x_1388_, v___x_1389_);
lean_dec(v___x_1388_);
return v___x_1390_;
}
}
}
static lean_object* _init_l_Lean_Expr_updateLambdaS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; 
v___x_1393_ = ((lean_object*)(l_Lean_Expr_updateLambdaS_x21___redArg___closed__1));
v___x_1394_ = lean_unsigned_to_nat(27u);
v___x_1395_ = lean_unsigned_to_nat(167u);
v___x_1396_ = ((lean_object*)(l_Lean_Expr_updateLambdaS_x21___redArg___closed__0));
v___x_1397_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1398_ = l_mkPanicMessageWithDecl(v___x_1397_, v___x_1396_, v___x_1395_, v___x_1394_, v___x_1393_);
return v___x_1398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLambdaS_x21___redArg(lean_object* v_inst_1399_, lean_object* v_inst_1400_, lean_object* v_e_1401_, lean_object* v_newDomain_1402_, lean_object* v_newBody_1403_){
_start:
{
if (lean_obj_tag(v_e_1401_) == 6)
{
lean_object* v_toApplicative_1404_; lean_object* v_toPure_1405_; lean_object* v_binderName_1406_; lean_object* v_binderType_1407_; lean_object* v_body_1408_; uint8_t v_binderInfo_1409_; size_t v___x_1410_; size_t v___x_1411_; uint8_t v___x_1412_; 
v_toApplicative_1404_ = lean_ctor_get(v_inst_1400_, 0);
v_toPure_1405_ = lean_ctor_get(v_toApplicative_1404_, 1);
v_binderName_1406_ = lean_ctor_get(v_e_1401_, 0);
v_binderType_1407_ = lean_ctor_get(v_e_1401_, 1);
v_body_1408_ = lean_ctor_get(v_e_1401_, 2);
v_binderInfo_1409_ = lean_ctor_get_uint8(v_e_1401_, sizeof(void*)*3 + 8);
v___x_1410_ = lean_ptr_addr(v_binderType_1407_);
v___x_1411_ = lean_ptr_addr(v_newDomain_1402_);
v___x_1412_ = lean_usize_dec_eq(v___x_1410_, v___x_1411_);
if (v___x_1412_ == 0)
{
lean_object* v___x_1413_; 
lean_inc(v_binderName_1406_);
lean_dec_ref_known(v_e_1401_, 3);
v___x_1413_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v_inst_1399_, v_inst_1400_, v_binderName_1406_, v_binderInfo_1409_, v_newDomain_1402_, v_newBody_1403_);
return v___x_1413_;
}
else
{
size_t v___x_1414_; size_t v___x_1415_; uint8_t v___x_1416_; 
v___x_1414_ = lean_ptr_addr(v_body_1408_);
v___x_1415_ = lean_ptr_addr(v_newBody_1403_);
v___x_1416_ = lean_usize_dec_eq(v___x_1414_, v___x_1415_);
if (v___x_1416_ == 0)
{
lean_object* v___x_1417_; 
lean_inc(v_binderName_1406_);
lean_dec_ref_known(v_e_1401_, 3);
v___x_1417_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v_inst_1399_, v_inst_1400_, v_binderName_1406_, v_binderInfo_1409_, v_newDomain_1402_, v_newBody_1403_);
return v___x_1417_;
}
else
{
lean_object* v___x_1418_; 
lean_inc(v_toPure_1405_);
lean_dec_ref(v_newBody_1403_);
lean_dec_ref(v_newDomain_1402_);
lean_dec_ref(v_inst_1400_);
lean_dec_ref(v_inst_1399_);
v___x_1418_ = lean_apply_2(v_toPure_1405_, lean_box(0), v_e_1401_);
return v___x_1418_;
}
}
}
else
{
lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; 
lean_dec_ref(v_newBody_1403_);
lean_dec_ref(v_newDomain_1402_);
lean_dec_ref(v_e_1401_);
lean_dec_ref(v_inst_1399_);
v___x_1419_ = l_Lean_instInhabitedExpr;
v___x_1420_ = l_instInhabitedOfMonad___redArg(v_inst_1400_, v___x_1419_);
v___x_1421_ = lean_obj_once(&l_Lean_Expr_updateLambdaS_x21___redArg___closed__2, &l_Lean_Expr_updateLambdaS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateLambdaS_x21___redArg___closed__2);
v___x_1422_ = l_panic___redArg(v___x_1420_, v___x_1421_);
lean_dec(v___x_1420_);
return v___x_1422_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLambdaS_x21(lean_object* v_m_1423_, lean_object* v_inst_1424_, lean_object* v_inst_1425_, lean_object* v_e_1426_, lean_object* v_newDomain_1427_, lean_object* v_newBody_1428_){
_start:
{
if (lean_obj_tag(v_e_1426_) == 6)
{
lean_object* v_toApplicative_1429_; lean_object* v_toPure_1430_; lean_object* v_binderName_1431_; lean_object* v_binderType_1432_; lean_object* v_body_1433_; uint8_t v_binderInfo_1434_; size_t v___x_1435_; size_t v___x_1436_; uint8_t v___x_1437_; 
v_toApplicative_1429_ = lean_ctor_get(v_inst_1425_, 0);
v_toPure_1430_ = lean_ctor_get(v_toApplicative_1429_, 1);
v_binderName_1431_ = lean_ctor_get(v_e_1426_, 0);
v_binderType_1432_ = lean_ctor_get(v_e_1426_, 1);
v_body_1433_ = lean_ctor_get(v_e_1426_, 2);
v_binderInfo_1434_ = lean_ctor_get_uint8(v_e_1426_, sizeof(void*)*3 + 8);
v___x_1435_ = lean_ptr_addr(v_binderType_1432_);
v___x_1436_ = lean_ptr_addr(v_newDomain_1427_);
v___x_1437_ = lean_usize_dec_eq(v___x_1435_, v___x_1436_);
if (v___x_1437_ == 0)
{
lean_object* v___x_1438_; 
lean_inc(v_binderName_1431_);
lean_dec_ref_known(v_e_1426_, 3);
v___x_1438_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v_inst_1424_, v_inst_1425_, v_binderName_1431_, v_binderInfo_1434_, v_newDomain_1427_, v_newBody_1428_);
return v___x_1438_;
}
else
{
size_t v___x_1439_; size_t v___x_1440_; uint8_t v___x_1441_; 
v___x_1439_ = lean_ptr_addr(v_body_1433_);
v___x_1440_ = lean_ptr_addr(v_newBody_1428_);
v___x_1441_ = lean_usize_dec_eq(v___x_1439_, v___x_1440_);
if (v___x_1441_ == 0)
{
lean_object* v___x_1442_; 
lean_inc(v_binderName_1431_);
lean_dec_ref_known(v_e_1426_, 3);
v___x_1442_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v_inst_1424_, v_inst_1425_, v_binderName_1431_, v_binderInfo_1434_, v_newDomain_1427_, v_newBody_1428_);
return v___x_1442_;
}
else
{
lean_object* v___x_1443_; 
lean_inc(v_toPure_1430_);
lean_dec_ref(v_newBody_1428_);
lean_dec_ref(v_newDomain_1427_);
lean_dec_ref(v_inst_1425_);
lean_dec_ref(v_inst_1424_);
v___x_1443_ = lean_apply_2(v_toPure_1430_, lean_box(0), v_e_1426_);
return v___x_1443_;
}
}
}
else
{
lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; 
lean_dec_ref(v_newBody_1428_);
lean_dec_ref(v_newDomain_1427_);
lean_dec_ref(v_e_1426_);
lean_dec_ref(v_inst_1424_);
v___x_1444_ = l_Lean_instInhabitedExpr;
v___x_1445_ = l_instInhabitedOfMonad___redArg(v_inst_1425_, v___x_1444_);
v___x_1446_ = lean_obj_once(&l_Lean_Expr_updateLambdaS_x21___redArg___closed__2, &l_Lean_Expr_updateLambdaS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateLambdaS_x21___redArg___closed__2);
v___x_1447_ = l_panic___redArg(v___x_1445_, v___x_1446_);
lean_dec(v___x_1445_);
return v___x_1447_;
}
}
}
static lean_object* _init_l_Lean_Expr_updateLetS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; 
v___x_1450_ = ((lean_object*)(l_Lean_Expr_updateLetS_x21___redArg___closed__1));
v___x_1451_ = lean_unsigned_to_nat(34u);
v___x_1452_ = lean_unsigned_to_nat(174u);
v___x_1453_ = ((lean_object*)(l_Lean_Expr_updateLetS_x21___redArg___closed__0));
v___x_1454_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1455_ = l_mkPanicMessageWithDecl(v___x_1454_, v___x_1453_, v___x_1452_, v___x_1451_, v___x_1450_);
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLetS_x21___redArg(lean_object* v_inst_1456_, lean_object* v_inst_1457_, lean_object* v_e_1458_, lean_object* v_newType_1459_, lean_object* v_newVal_1460_, lean_object* v_newBody_1461_){
_start:
{
if (lean_obj_tag(v_e_1458_) == 8)
{
lean_object* v_toApplicative_1462_; lean_object* v_toPure_1463_; lean_object* v_declName_1464_; lean_object* v_type_1465_; lean_object* v_value_1466_; lean_object* v_body_1467_; uint8_t v_nondep_1468_; size_t v___x_1469_; size_t v___x_1470_; uint8_t v___x_1471_; 
v_toApplicative_1462_ = lean_ctor_get(v_inst_1457_, 0);
v_toPure_1463_ = lean_ctor_get(v_toApplicative_1462_, 1);
v_declName_1464_ = lean_ctor_get(v_e_1458_, 0);
v_type_1465_ = lean_ctor_get(v_e_1458_, 1);
v_value_1466_ = lean_ctor_get(v_e_1458_, 2);
v_body_1467_ = lean_ctor_get(v_e_1458_, 3);
v_nondep_1468_ = lean_ctor_get_uint8(v_e_1458_, sizeof(void*)*4 + 8);
v___x_1469_ = lean_ptr_addr(v_type_1465_);
v___x_1470_ = lean_ptr_addr(v_newType_1459_);
v___x_1471_ = lean_usize_dec_eq(v___x_1469_, v___x_1470_);
if (v___x_1471_ == 0)
{
lean_object* v___x_1472_; 
lean_inc(v_declName_1464_);
lean_dec_ref_known(v_e_1458_, 4);
v___x_1472_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1456_, v_inst_1457_, v_declName_1464_, v_newType_1459_, v_newVal_1460_, v_newBody_1461_, v_nondep_1468_);
return v___x_1472_;
}
else
{
size_t v___x_1473_; size_t v___x_1474_; uint8_t v___x_1475_; 
v___x_1473_ = lean_ptr_addr(v_value_1466_);
v___x_1474_ = lean_ptr_addr(v_newVal_1460_);
v___x_1475_ = lean_usize_dec_eq(v___x_1473_, v___x_1474_);
if (v___x_1475_ == 0)
{
lean_object* v___x_1476_; 
lean_inc(v_declName_1464_);
lean_dec_ref_known(v_e_1458_, 4);
v___x_1476_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1456_, v_inst_1457_, v_declName_1464_, v_newType_1459_, v_newVal_1460_, v_newBody_1461_, v_nondep_1468_);
return v___x_1476_;
}
else
{
size_t v___x_1477_; size_t v___x_1478_; uint8_t v___x_1479_; 
v___x_1477_ = lean_ptr_addr(v_body_1467_);
v___x_1478_ = lean_ptr_addr(v_newBody_1461_);
v___x_1479_ = lean_usize_dec_eq(v___x_1477_, v___x_1478_);
if (v___x_1479_ == 0)
{
lean_object* v___x_1480_; 
lean_inc(v_declName_1464_);
lean_dec_ref_known(v_e_1458_, 4);
v___x_1480_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1456_, v_inst_1457_, v_declName_1464_, v_newType_1459_, v_newVal_1460_, v_newBody_1461_, v_nondep_1468_);
return v___x_1480_;
}
else
{
lean_object* v___x_1481_; 
lean_inc(v_toPure_1463_);
lean_dec_ref(v_newBody_1461_);
lean_dec_ref(v_newVal_1460_);
lean_dec_ref(v_newType_1459_);
lean_dec_ref(v_inst_1457_);
lean_dec_ref(v_inst_1456_);
v___x_1481_ = lean_apply_2(v_toPure_1463_, lean_box(0), v_e_1458_);
return v___x_1481_;
}
}
}
}
else
{
lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; 
lean_dec_ref(v_newBody_1461_);
lean_dec_ref(v_newVal_1460_);
lean_dec_ref(v_newType_1459_);
lean_dec_ref(v_e_1458_);
lean_dec_ref(v_inst_1456_);
v___x_1482_ = l_Lean_instInhabitedExpr;
v___x_1483_ = l_instInhabitedOfMonad___redArg(v_inst_1457_, v___x_1482_);
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
lean_object* v_toApplicative_1493_; lean_object* v_toPure_1494_; lean_object* v_declName_1495_; lean_object* v_type_1496_; lean_object* v_value_1497_; lean_object* v_body_1498_; uint8_t v_nondep_1499_; size_t v___x_1500_; size_t v___x_1501_; uint8_t v___x_1502_; 
v_toApplicative_1493_ = lean_ctor_get(v_inst_1488_, 0);
v_toPure_1494_ = lean_ctor_get(v_toApplicative_1493_, 1);
v_declName_1495_ = lean_ctor_get(v_e_1489_, 0);
v_type_1496_ = lean_ctor_get(v_e_1489_, 1);
v_value_1497_ = lean_ctor_get(v_e_1489_, 2);
v_body_1498_ = lean_ctor_get(v_e_1489_, 3);
v_nondep_1499_ = lean_ctor_get_uint8(v_e_1489_, sizeof(void*)*4 + 8);
v___x_1500_ = lean_ptr_addr(v_type_1496_);
v___x_1501_ = lean_ptr_addr(v_newType_1490_);
v___x_1502_ = lean_usize_dec_eq(v___x_1500_, v___x_1501_);
if (v___x_1502_ == 0)
{
lean_object* v___x_1503_; 
lean_inc(v_declName_1495_);
lean_dec_ref_known(v_e_1489_, 4);
v___x_1503_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1487_, v_inst_1488_, v_declName_1495_, v_newType_1490_, v_newVal_1491_, v_newBody_1492_, v_nondep_1499_);
return v___x_1503_;
}
else
{
size_t v___x_1504_; size_t v___x_1505_; uint8_t v___x_1506_; 
v___x_1504_ = lean_ptr_addr(v_value_1497_);
v___x_1505_ = lean_ptr_addr(v_newVal_1491_);
v___x_1506_ = lean_usize_dec_eq(v___x_1504_, v___x_1505_);
if (v___x_1506_ == 0)
{
lean_object* v___x_1507_; 
lean_inc(v_declName_1495_);
lean_dec_ref_known(v_e_1489_, 4);
v___x_1507_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1487_, v_inst_1488_, v_declName_1495_, v_newType_1490_, v_newVal_1491_, v_newBody_1492_, v_nondep_1499_);
return v___x_1507_;
}
else
{
size_t v___x_1508_; size_t v___x_1509_; uint8_t v___x_1510_; 
v___x_1508_ = lean_ptr_addr(v_body_1498_);
v___x_1509_ = lean_ptr_addr(v_newBody_1492_);
v___x_1510_ = lean_usize_dec_eq(v___x_1508_, v___x_1509_);
if (v___x_1510_ == 0)
{
lean_object* v___x_1511_; 
lean_inc(v_declName_1495_);
lean_dec_ref_known(v_e_1489_, 4);
v___x_1511_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1487_, v_inst_1488_, v_declName_1495_, v_newType_1490_, v_newVal_1491_, v_newBody_1492_, v_nondep_1499_);
return v___x_1511_;
}
else
{
lean_object* v___x_1512_; 
lean_inc(v_toPure_1494_);
lean_dec_ref(v_newBody_1492_);
lean_dec_ref(v_newVal_1491_);
lean_dec_ref(v_newType_1490_);
lean_dec_ref(v_inst_1488_);
lean_dec_ref(v_inst_1487_);
v___x_1512_ = lean_apply_2(v_toPure_1494_, lean_box(0), v_e_1489_);
return v___x_1512_;
}
}
}
}
else
{
lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; 
lean_dec_ref(v_newBody_1492_);
lean_dec_ref(v_newVal_1491_);
lean_dec_ref(v_newType_1490_);
lean_dec_ref(v_e_1489_);
lean_dec_ref(v_inst_1487_);
v___x_1513_ = l_Lean_instInhabitedExpr;
v___x_1514_ = l_instInhabitedOfMonad___redArg(v_inst_1488_, v___x_1513_);
v___x_1515_ = lean_obj_once(&l_Lean_Expr_updateLetS_x21___redArg___closed__2, &l_Lean_Expr_updateLetS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateLetS_x21___redArg___closed__2);
v___x_1516_ = l_panic___redArg(v___x_1514_, v___x_1515_);
lean_dec(v___x_1514_);
return v___x_1516_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___redArg___lam__0(lean_object* v_inst_1517_, lean_object* v_inst_1518_, lean_object* v_a_u2082_1519_, lean_object* v_____do__lift_1520_){
_start:
{
lean_object* v___x_1521_; 
v___x_1521_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1517_, v_inst_1518_, v_____do__lift_1520_, v_a_u2082_1519_);
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___redArg(lean_object* v_inst_1522_, lean_object* v_inst_1523_, lean_object* v_f_1524_, lean_object* v_a_u2081_1525_, lean_object* v_a_u2082_1526_){
_start:
{
lean_object* v_toBind_1527_; lean_object* v___f_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; 
v_toBind_1527_ = lean_ctor_get(v_inst_1523_, 1);
lean_inc(v_toBind_1527_);
lean_inc_ref(v_inst_1523_);
lean_inc_ref(v_inst_1522_);
v___f_1528_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2082___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1528_, 0, v_inst_1522_);
lean_closure_set(v___f_1528_, 1, v_inst_1523_);
lean_closure_set(v___f_1528_, 2, v_a_u2082_1526_);
v___x_1529_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1522_, v_inst_1523_, v_f_1524_, v_a_u2081_1525_);
v___x_1530_ = lean_apply_4(v_toBind_1527_, lean_box(0), lean_box(0), v___x_1529_, v___f_1528_);
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082(lean_object* v_m_1531_, lean_object* v_inst_1532_, lean_object* v_inst_1533_, lean_object* v_f_1534_, lean_object* v_a_u2081_1535_, lean_object* v_a_u2082_1536_){
_start:
{
lean_object* v___x_1537_; 
v___x_1537_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___redArg(v_inst_1532_, v_inst_1533_, v_f_1534_, v_a_u2081_1535_, v_a_u2082_1536_);
return v___x_1537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___redArg___lam__0(lean_object* v_inst_1538_, lean_object* v_inst_1539_, lean_object* v_a_u2083_1540_, lean_object* v_____do__lift_1541_){
_start:
{
lean_object* v___x_1542_; 
v___x_1542_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1538_, v_inst_1539_, v_____do__lift_1541_, v_a_u2083_1540_);
return v___x_1542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___redArg(lean_object* v_inst_1543_, lean_object* v_inst_1544_, lean_object* v_f_1545_, lean_object* v_a_u2081_1546_, lean_object* v_a_u2082_1547_, lean_object* v_a_u2083_1548_){
_start:
{
lean_object* v_toBind_1549_; lean_object* v___f_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; 
v_toBind_1549_ = lean_ctor_get(v_inst_1544_, 1);
lean_inc(v_toBind_1549_);
lean_inc_ref(v_inst_1544_);
lean_inc_ref(v_inst_1543_);
v___f_1550_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2083___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1550_, 0, v_inst_1543_);
lean_closure_set(v___f_1550_, 1, v_inst_1544_);
lean_closure_set(v___f_1550_, 2, v_a_u2083_1548_);
v___x_1551_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___redArg(v_inst_1543_, v_inst_1544_, v_f_1545_, v_a_u2081_1546_, v_a_u2082_1547_);
v___x_1552_ = lean_apply_4(v_toBind_1549_, lean_box(0), lean_box(0), v___x_1551_, v___f_1550_);
return v___x_1552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083(lean_object* v_m_1553_, lean_object* v_inst_1554_, lean_object* v_inst_1555_, lean_object* v_f_1556_, lean_object* v_a_u2081_1557_, lean_object* v_a_u2082_1558_, lean_object* v_a_u2083_1559_){
_start:
{
lean_object* v___x_1560_; 
v___x_1560_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___redArg(v_inst_1554_, v_inst_1555_, v_f_1556_, v_a_u2081_1557_, v_a_u2082_1558_, v_a_u2083_1559_);
return v___x_1560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___redArg___lam__0(lean_object* v_inst_1561_, lean_object* v_inst_1562_, lean_object* v_a_u2084_1563_, lean_object* v_____do__lift_1564_){
_start:
{
lean_object* v___x_1565_; 
v___x_1565_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1561_, v_inst_1562_, v_____do__lift_1564_, v_a_u2084_1563_);
return v___x_1565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___redArg(lean_object* v_inst_1566_, lean_object* v_inst_1567_, lean_object* v_f_1568_, lean_object* v_a_u2081_1569_, lean_object* v_a_u2082_1570_, lean_object* v_a_u2083_1571_, lean_object* v_a_u2084_1572_){
_start:
{
lean_object* v_toBind_1573_; lean_object* v___f_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; 
v_toBind_1573_ = lean_ctor_get(v_inst_1567_, 1);
lean_inc(v_toBind_1573_);
lean_inc_ref(v_inst_1567_);
lean_inc_ref(v_inst_1566_);
v___f_1574_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2084___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1574_, 0, v_inst_1566_);
lean_closure_set(v___f_1574_, 1, v_inst_1567_);
lean_closure_set(v___f_1574_, 2, v_a_u2084_1572_);
v___x_1575_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___redArg(v_inst_1566_, v_inst_1567_, v_f_1568_, v_a_u2081_1569_, v_a_u2082_1570_, v_a_u2083_1571_);
v___x_1576_ = lean_apply_4(v_toBind_1573_, lean_box(0), lean_box(0), v___x_1575_, v___f_1574_);
return v___x_1576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084(lean_object* v_m_1577_, lean_object* v_inst_1578_, lean_object* v_inst_1579_, lean_object* v_f_1580_, lean_object* v_a_u2081_1581_, lean_object* v_a_u2082_1582_, lean_object* v_a_u2083_1583_, lean_object* v_a_u2084_1584_){
_start:
{
lean_object* v___x_1585_; 
v___x_1585_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___redArg(v_inst_1578_, v_inst_1579_, v_f_1580_, v_a_u2081_1581_, v_a_u2082_1582_, v_a_u2083_1583_, v_a_u2084_1584_);
return v___x_1585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2085___redArg___lam__0(lean_object* v_inst_1586_, lean_object* v_inst_1587_, lean_object* v_a_u2085_1588_, lean_object* v_____do__lift_1589_){
_start:
{
lean_object* v___x_1590_; 
v___x_1590_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1586_, v_inst_1587_, v_____do__lift_1589_, v_a_u2085_1588_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2085___redArg(lean_object* v_inst_1591_, lean_object* v_inst_1592_, lean_object* v_f_1593_, lean_object* v_a_u2081_1594_, lean_object* v_a_u2082_1595_, lean_object* v_a_u2083_1596_, lean_object* v_a_u2084_1597_, lean_object* v_a_u2085_1598_){
_start:
{
lean_object* v_toBind_1599_; lean_object* v___f_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; 
v_toBind_1599_ = lean_ctor_get(v_inst_1592_, 1);
lean_inc(v_toBind_1599_);
lean_inc_ref(v_inst_1592_);
lean_inc_ref(v_inst_1591_);
v___f_1600_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2085___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1600_, 0, v_inst_1591_);
lean_closure_set(v___f_1600_, 1, v_inst_1592_);
lean_closure_set(v___f_1600_, 2, v_a_u2085_1598_);
v___x_1601_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___redArg(v_inst_1591_, v_inst_1592_, v_f_1593_, v_a_u2081_1594_, v_a_u2082_1595_, v_a_u2083_1596_, v_a_u2084_1597_);
v___x_1602_ = lean_apply_4(v_toBind_1599_, lean_box(0), lean_box(0), v___x_1601_, v___f_1600_);
return v___x_1602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2085(lean_object* v_m_1603_, lean_object* v_inst_1604_, lean_object* v_inst_1605_, lean_object* v_f_1606_, lean_object* v_a_u2081_1607_, lean_object* v_a_u2082_1608_, lean_object* v_a_u2083_1609_, lean_object* v_a_u2084_1610_, lean_object* v_a_u2085_1611_){
_start:
{
lean_object* v___x_1612_; 
v___x_1612_ = l_Lean_Meta_Sym_Internal_mkAppS_u2085___redArg(v_inst_1604_, v_inst_1605_, v_f_1606_, v_a_u2081_1607_, v_a_u2082_1608_, v_a_u2083_1609_, v_a_u2084_1610_, v_a_u2085_1611_);
return v___x_1612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2086___redArg___lam__0(lean_object* v_inst_1613_, lean_object* v_inst_1614_, lean_object* v_a_u2086_1615_, lean_object* v_____do__lift_1616_){
_start:
{
lean_object* v___x_1617_; 
v___x_1617_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1613_, v_inst_1614_, v_____do__lift_1616_, v_a_u2086_1615_);
return v___x_1617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2086___redArg(lean_object* v_inst_1618_, lean_object* v_inst_1619_, lean_object* v_f_1620_, lean_object* v_a_u2081_1621_, lean_object* v_a_u2082_1622_, lean_object* v_a_u2083_1623_, lean_object* v_a_u2084_1624_, lean_object* v_a_u2085_1625_, lean_object* v_a_u2086_1626_){
_start:
{
lean_object* v_toBind_1627_; lean_object* v___f_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; 
v_toBind_1627_ = lean_ctor_get(v_inst_1619_, 1);
lean_inc(v_toBind_1627_);
lean_inc_ref(v_inst_1619_);
lean_inc_ref(v_inst_1618_);
v___f_1628_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2086___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1628_, 0, v_inst_1618_);
lean_closure_set(v___f_1628_, 1, v_inst_1619_);
lean_closure_set(v___f_1628_, 2, v_a_u2086_1626_);
v___x_1629_ = l_Lean_Meta_Sym_Internal_mkAppS_u2085___redArg(v_inst_1618_, v_inst_1619_, v_f_1620_, v_a_u2081_1621_, v_a_u2082_1622_, v_a_u2083_1623_, v_a_u2084_1624_, v_a_u2085_1625_);
v___x_1630_ = lean_apply_4(v_toBind_1627_, lean_box(0), lean_box(0), v___x_1629_, v___f_1628_);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2086(lean_object* v_m_1631_, lean_object* v_inst_1632_, lean_object* v_inst_1633_, lean_object* v_f_1634_, lean_object* v_a_u2081_1635_, lean_object* v_a_u2082_1636_, lean_object* v_a_u2083_1637_, lean_object* v_a_u2084_1638_, lean_object* v_a_u2085_1639_, lean_object* v_a_u2086_1640_){
_start:
{
lean_object* v___x_1641_; 
v___x_1641_ = l_Lean_Meta_Sym_Internal_mkAppS_u2086___redArg(v_inst_1632_, v_inst_1633_, v_f_1634_, v_a_u2081_1635_, v_a_u2082_1636_, v_a_u2083_1637_, v_a_u2084_1638_, v_a_u2085_1639_, v_a_u2086_1640_);
return v___x_1641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2087___redArg___lam__0(lean_object* v_inst_1642_, lean_object* v_inst_1643_, lean_object* v_a_u2087_1644_, lean_object* v_____do__lift_1645_){
_start:
{
lean_object* v___x_1646_; 
v___x_1646_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1642_, v_inst_1643_, v_____do__lift_1645_, v_a_u2087_1644_);
return v___x_1646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2087___redArg(lean_object* v_inst_1647_, lean_object* v_inst_1648_, lean_object* v_f_1649_, lean_object* v_a_u2081_1650_, lean_object* v_a_u2082_1651_, lean_object* v_a_u2083_1652_, lean_object* v_a_u2084_1653_, lean_object* v_a_u2085_1654_, lean_object* v_a_u2086_1655_, lean_object* v_a_u2087_1656_){
_start:
{
lean_object* v_toBind_1657_; lean_object* v___f_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; 
v_toBind_1657_ = lean_ctor_get(v_inst_1648_, 1);
lean_inc(v_toBind_1657_);
lean_inc_ref(v_inst_1648_);
lean_inc_ref(v_inst_1647_);
v___f_1658_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2087___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1658_, 0, v_inst_1647_);
lean_closure_set(v___f_1658_, 1, v_inst_1648_);
lean_closure_set(v___f_1658_, 2, v_a_u2087_1656_);
v___x_1659_ = l_Lean_Meta_Sym_Internal_mkAppS_u2086___redArg(v_inst_1647_, v_inst_1648_, v_f_1649_, v_a_u2081_1650_, v_a_u2082_1651_, v_a_u2083_1652_, v_a_u2084_1653_, v_a_u2085_1654_, v_a_u2086_1655_);
v___x_1660_ = lean_apply_4(v_toBind_1657_, lean_box(0), lean_box(0), v___x_1659_, v___f_1658_);
return v___x_1660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2087(lean_object* v_m_1661_, lean_object* v_inst_1662_, lean_object* v_inst_1663_, lean_object* v_f_1664_, lean_object* v_a_u2081_1665_, lean_object* v_a_u2082_1666_, lean_object* v_a_u2083_1667_, lean_object* v_a_u2084_1668_, lean_object* v_a_u2085_1669_, lean_object* v_a_u2086_1670_, lean_object* v_a_u2087_1671_){
_start:
{
lean_object* v___x_1672_; 
v___x_1672_ = l_Lean_Meta_Sym_Internal_mkAppS_u2087___redArg(v_inst_1662_, v_inst_1663_, v_f_1664_, v_a_u2081_1665_, v_a_u2082_1666_, v_a_u2083_1667_, v_a_u2084_1668_, v_a_u2085_1669_, v_a_u2086_1670_, v_a_u2087_1671_);
return v___x_1672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2088___redArg___lam__0(lean_object* v_inst_1673_, lean_object* v_inst_1674_, lean_object* v_a_u2088_1675_, lean_object* v_____do__lift_1676_){
_start:
{
lean_object* v___x_1677_; 
v___x_1677_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1673_, v_inst_1674_, v_____do__lift_1676_, v_a_u2088_1675_);
return v___x_1677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2088___redArg(lean_object* v_inst_1678_, lean_object* v_inst_1679_, lean_object* v_f_1680_, lean_object* v_a_u2081_1681_, lean_object* v_a_u2082_1682_, lean_object* v_a_u2083_1683_, lean_object* v_a_u2084_1684_, lean_object* v_a_u2085_1685_, lean_object* v_a_u2086_1686_, lean_object* v_a_u2087_1687_, lean_object* v_a_u2088_1688_){
_start:
{
lean_object* v_toBind_1689_; lean_object* v___f_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; 
v_toBind_1689_ = lean_ctor_get(v_inst_1679_, 1);
lean_inc(v_toBind_1689_);
lean_inc_ref(v_inst_1679_);
lean_inc_ref(v_inst_1678_);
v___f_1690_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2088___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1690_, 0, v_inst_1678_);
lean_closure_set(v___f_1690_, 1, v_inst_1679_);
lean_closure_set(v___f_1690_, 2, v_a_u2088_1688_);
v___x_1691_ = l_Lean_Meta_Sym_Internal_mkAppS_u2087___redArg(v_inst_1678_, v_inst_1679_, v_f_1680_, v_a_u2081_1681_, v_a_u2082_1682_, v_a_u2083_1683_, v_a_u2084_1684_, v_a_u2085_1685_, v_a_u2086_1686_, v_a_u2087_1687_);
v___x_1692_ = lean_apply_4(v_toBind_1689_, lean_box(0), lean_box(0), v___x_1691_, v___f_1690_);
return v___x_1692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2088(lean_object* v_m_1693_, lean_object* v_inst_1694_, lean_object* v_inst_1695_, lean_object* v_f_1696_, lean_object* v_a_u2081_1697_, lean_object* v_a_u2082_1698_, lean_object* v_a_u2083_1699_, lean_object* v_a_u2084_1700_, lean_object* v_a_u2085_1701_, lean_object* v_a_u2086_1702_, lean_object* v_a_u2087_1703_, lean_object* v_a_u2088_1704_){
_start:
{
lean_object* v___x_1705_; 
v___x_1705_ = l_Lean_Meta_Sym_Internal_mkAppS_u2088___redArg(v_inst_1694_, v_inst_1695_, v_f_1696_, v_a_u2081_1697_, v_a_u2082_1698_, v_a_u2083_1699_, v_a_u2084_1700_, v_a_u2085_1701_, v_a_u2086_1702_, v_a_u2087_1703_, v_a_u2088_1704_);
return v___x_1705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2089___redArg___lam__0(lean_object* v_inst_1706_, lean_object* v_inst_1707_, lean_object* v_a_u2089_1708_, lean_object* v_____do__lift_1709_){
_start:
{
lean_object* v___x_1710_; 
v___x_1710_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1706_, v_inst_1707_, v_____do__lift_1709_, v_a_u2089_1708_);
return v___x_1710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2089___redArg(lean_object* v_inst_1711_, lean_object* v_inst_1712_, lean_object* v_f_1713_, lean_object* v_a_u2081_1714_, lean_object* v_a_u2082_1715_, lean_object* v_a_u2083_1716_, lean_object* v_a_u2084_1717_, lean_object* v_a_u2085_1718_, lean_object* v_a_u2086_1719_, lean_object* v_a_u2087_1720_, lean_object* v_a_u2088_1721_, lean_object* v_a_u2089_1722_){
_start:
{
lean_object* v_toBind_1723_; lean_object* v___f_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; 
v_toBind_1723_ = lean_ctor_get(v_inst_1712_, 1);
lean_inc(v_toBind_1723_);
lean_inc_ref(v_inst_1712_);
lean_inc_ref(v_inst_1711_);
v___f_1724_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2089___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1724_, 0, v_inst_1711_);
lean_closure_set(v___f_1724_, 1, v_inst_1712_);
lean_closure_set(v___f_1724_, 2, v_a_u2089_1722_);
v___x_1725_ = l_Lean_Meta_Sym_Internal_mkAppS_u2088___redArg(v_inst_1711_, v_inst_1712_, v_f_1713_, v_a_u2081_1714_, v_a_u2082_1715_, v_a_u2083_1716_, v_a_u2084_1717_, v_a_u2085_1718_, v_a_u2086_1719_, v_a_u2087_1720_, v_a_u2088_1721_);
v___x_1726_ = lean_apply_4(v_toBind_1723_, lean_box(0), lean_box(0), v___x_1725_, v___f_1724_);
return v___x_1726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2089(lean_object* v_m_1727_, lean_object* v_inst_1728_, lean_object* v_inst_1729_, lean_object* v_f_1730_, lean_object* v_a_u2081_1731_, lean_object* v_a_u2082_1732_, lean_object* v_a_u2083_1733_, lean_object* v_a_u2084_1734_, lean_object* v_a_u2085_1735_, lean_object* v_a_u2086_1736_, lean_object* v_a_u2087_1737_, lean_object* v_a_u2088_1738_, lean_object* v_a_u2089_1739_){
_start:
{
lean_object* v___x_1740_; 
v___x_1740_ = l_Lean_Meta_Sym_Internal_mkAppS_u2089___redArg(v_inst_1728_, v_inst_1729_, v_f_1730_, v_a_u2081_1731_, v_a_u2082_1732_, v_a_u2083_1733_, v_a_u2084_1734_, v_a_u2085_1735_, v_a_u2086_1736_, v_a_u2087_1737_, v_a_u2088_1738_, v_a_u2089_1739_);
return v___x_1740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2080___redArg___lam__0(lean_object* v_inst_1741_, lean_object* v_inst_1742_, lean_object* v_a_u2081_u2080_1743_, lean_object* v_____do__lift_1744_){
_start:
{
lean_object* v___x_1745_; 
v___x_1745_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1741_, v_inst_1742_, v_____do__lift_1744_, v_a_u2081_u2080_1743_);
return v___x_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2080___redArg(lean_object* v_inst_1746_, lean_object* v_inst_1747_, lean_object* v_f_1748_, lean_object* v_a_u2081_1749_, lean_object* v_a_u2082_1750_, lean_object* v_a_u2083_1751_, lean_object* v_a_u2084_1752_, lean_object* v_a_u2085_1753_, lean_object* v_a_u2086_1754_, lean_object* v_a_u2087_1755_, lean_object* v_a_u2088_1756_, lean_object* v_a_u2089_1757_, lean_object* v_a_u2081_u2080_1758_){
_start:
{
lean_object* v_toBind_1759_; lean_object* v___f_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; 
v_toBind_1759_ = lean_ctor_get(v_inst_1747_, 1);
lean_inc(v_toBind_1759_);
lean_inc_ref(v_inst_1747_);
lean_inc_ref(v_inst_1746_);
v___f_1760_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2080___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1760_, 0, v_inst_1746_);
lean_closure_set(v___f_1760_, 1, v_inst_1747_);
lean_closure_set(v___f_1760_, 2, v_a_u2081_u2080_1758_);
v___x_1761_ = l_Lean_Meta_Sym_Internal_mkAppS_u2089___redArg(v_inst_1746_, v_inst_1747_, v_f_1748_, v_a_u2081_1749_, v_a_u2082_1750_, v_a_u2083_1751_, v_a_u2084_1752_, v_a_u2085_1753_, v_a_u2086_1754_, v_a_u2087_1755_, v_a_u2088_1756_, v_a_u2089_1757_);
v___x_1762_ = lean_apply_4(v_toBind_1759_, lean_box(0), lean_box(0), v___x_1761_, v___f_1760_);
return v___x_1762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2080(lean_object* v_m_1763_, lean_object* v_inst_1764_, lean_object* v_inst_1765_, lean_object* v_f_1766_, lean_object* v_a_u2081_1767_, lean_object* v_a_u2082_1768_, lean_object* v_a_u2083_1769_, lean_object* v_a_u2084_1770_, lean_object* v_a_u2085_1771_, lean_object* v_a_u2086_1772_, lean_object* v_a_u2087_1773_, lean_object* v_a_u2088_1774_, lean_object* v_a_u2089_1775_, lean_object* v_a_u2081_u2080_1776_){
_start:
{
lean_object* v___x_1777_; 
v___x_1777_ = l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2080___redArg(v_inst_1764_, v_inst_1765_, v_f_1766_, v_a_u2081_1767_, v_a_u2082_1768_, v_a_u2083_1769_, v_a_u2084_1770_, v_a_u2085_1771_, v_a_u2086_1772_, v_a_u2087_1773_, v_a_u2088_1774_, v_a_u2089_1775_, v_a_u2081_u2080_1776_);
return v___x_1777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2081___redArg___lam__0(lean_object* v_inst_1778_, lean_object* v_inst_1779_, lean_object* v_a_u2081_u2081_1780_, lean_object* v_____do__lift_1781_){
_start:
{
lean_object* v___x_1782_; 
v___x_1782_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1778_, v_inst_1779_, v_____do__lift_1781_, v_a_u2081_u2081_1780_);
return v___x_1782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2081___redArg(lean_object* v_inst_1783_, lean_object* v_inst_1784_, lean_object* v_f_1785_, lean_object* v_a_u2081_1786_, lean_object* v_a_u2082_1787_, lean_object* v_a_u2083_1788_, lean_object* v_a_u2084_1789_, lean_object* v_a_u2085_1790_, lean_object* v_a_u2086_1791_, lean_object* v_a_u2087_1792_, lean_object* v_a_u2088_1793_, lean_object* v_a_u2089_1794_, lean_object* v_a_u2081_u2080_1795_, lean_object* v_a_u2081_u2081_1796_){
_start:
{
lean_object* v_toBind_1797_; lean_object* v___f_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; 
v_toBind_1797_ = lean_ctor_get(v_inst_1784_, 1);
lean_inc(v_toBind_1797_);
lean_inc_ref(v_inst_1784_);
lean_inc_ref(v_inst_1783_);
v___f_1798_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2081___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1798_, 0, v_inst_1783_);
lean_closure_set(v___f_1798_, 1, v_inst_1784_);
lean_closure_set(v___f_1798_, 2, v_a_u2081_u2081_1796_);
v___x_1799_ = l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2080___redArg(v_inst_1783_, v_inst_1784_, v_f_1785_, v_a_u2081_1786_, v_a_u2082_1787_, v_a_u2083_1788_, v_a_u2084_1789_, v_a_u2085_1790_, v_a_u2086_1791_, v_a_u2087_1792_, v_a_u2088_1793_, v_a_u2089_1794_, v_a_u2081_u2080_1795_);
v___x_1800_ = lean_apply_4(v_toBind_1797_, lean_box(0), lean_box(0), v___x_1799_, v___f_1798_);
return v___x_1800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2081(lean_object* v_m_1801_, lean_object* v_inst_1802_, lean_object* v_inst_1803_, lean_object* v_f_1804_, lean_object* v_a_u2081_1805_, lean_object* v_a_u2082_1806_, lean_object* v_a_u2083_1807_, lean_object* v_a_u2084_1808_, lean_object* v_a_u2085_1809_, lean_object* v_a_u2086_1810_, lean_object* v_a_u2087_1811_, lean_object* v_a_u2088_1812_, lean_object* v_a_u2089_1813_, lean_object* v_a_u2081_u2080_1814_, lean_object* v_a_u2081_u2081_1815_){
_start:
{
lean_object* v___x_1816_; 
v___x_1816_ = l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2081___redArg(v_inst_1802_, v_inst_1803_, v_f_1804_, v_a_u2081_1805_, v_a_u2082_1806_, v_a_u2083_1807_, v_a_u2084_1808_, v_a_u2085_1809_, v_a_u2086_1810_, v_a_u2087_1811_, v_a_u2088_1812_, v_a_u2089_1813_, v_a_u2081_u2080_1814_, v_a_u2081_u2081_1815_);
return v___x_1816_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg___lam__0___boxed(lean_object* v_i_1817_, lean_object* v_inst_1818_, lean_object* v_inst_1819_, lean_object* v_args_1820_, lean_object* v_endIdx_1821_, lean_object* v_____do__lift_1822_){
_start:
{
lean_object* v_res_1823_; 
v_res_1823_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg___lam__0(v_i_1817_, v_inst_1818_, v_inst_1819_, v_args_1820_, v_endIdx_1821_, v_____do__lift_1822_);
lean_dec(v_i_1817_);
return v_res_1823_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg(lean_object* v_inst_1824_, lean_object* v_inst_1825_, lean_object* v_args_1826_, lean_object* v_endIdx_1827_, lean_object* v_b_1828_, lean_object* v_i_1829_){
_start:
{
lean_object* v_toApplicative_1830_; lean_object* v_toBind_1831_; lean_object* v_toPure_1832_; uint8_t v___x_1833_; 
v_toApplicative_1830_ = lean_ctor_get(v_inst_1825_, 0);
v_toBind_1831_ = lean_ctor_get(v_inst_1825_, 1);
lean_inc(v_toBind_1831_);
v_toPure_1832_ = lean_ctor_get(v_toApplicative_1830_, 1);
v___x_1833_ = lean_nat_dec_le(v_endIdx_1827_, v_i_1829_);
if (v___x_1833_ == 0)
{
lean_object* v___f_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; 
lean_inc_ref(v_args_1826_);
lean_inc_ref(v_inst_1825_);
lean_inc_ref(v_inst_1824_);
lean_inc(v_i_1829_);
v___f_1834_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1834_, 0, v_i_1829_);
lean_closure_set(v___f_1834_, 1, v_inst_1824_);
lean_closure_set(v___f_1834_, 2, v_inst_1825_);
lean_closure_set(v___f_1834_, 3, v_args_1826_);
lean_closure_set(v___f_1834_, 4, v_endIdx_1827_);
v___x_1835_ = l_Lean_instInhabitedExpr;
v___x_1836_ = lean_array_get(v___x_1835_, v_args_1826_, v_i_1829_);
lean_dec(v_i_1829_);
lean_dec_ref(v_args_1826_);
v___x_1837_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1824_, v_inst_1825_, v_b_1828_, v___x_1836_);
v___x_1838_ = lean_apply_4(v_toBind_1831_, lean_box(0), lean_box(0), v___x_1837_, v___f_1834_);
return v___x_1838_;
}
else
{
lean_object* v___x_1839_; 
lean_inc(v_toPure_1832_);
lean_dec(v_toBind_1831_);
lean_dec(v_i_1829_);
lean_dec(v_endIdx_1827_);
lean_dec_ref(v_args_1826_);
lean_dec_ref(v_inst_1825_);
lean_dec_ref(v_inst_1824_);
v___x_1839_ = lean_apply_2(v_toPure_1832_, lean_box(0), v_b_1828_);
return v___x_1839_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg___lam__0(lean_object* v_i_1840_, lean_object* v_inst_1841_, lean_object* v_inst_1842_, lean_object* v_args_1843_, lean_object* v_endIdx_1844_, lean_object* v_____do__lift_1845_){
_start:
{
lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; 
v___x_1846_ = lean_unsigned_to_nat(1u);
v___x_1847_ = lean_nat_add(v_i_1840_, v___x_1846_);
v___x_1848_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg(v_inst_1841_, v_inst_1842_, v_args_1843_, v_endIdx_1844_, v_____do__lift_1845_, v___x_1847_);
return v___x_1848_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go(lean_object* v_m_1849_, lean_object* v_inst_1850_, lean_object* v_inst_1851_, lean_object* v_args_1852_, lean_object* v_endIdx_1853_, lean_object* v_b_1854_, lean_object* v_i_1855_){
_start:
{
lean_object* v___x_1856_; 
v___x_1856_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg(v_inst_1850_, v_inst_1851_, v_args_1852_, v_endIdx_1853_, v_b_1854_, v_i_1855_);
return v___x_1856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRangeS___redArg(lean_object* v_inst_1857_, lean_object* v_inst_1858_, lean_object* v_f_1859_, lean_object* v_beginIdx_1860_, lean_object* v_endIdx_1861_, lean_object* v_args_1862_){
_start:
{
lean_object* v___x_1863_; 
v___x_1863_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg(v_inst_1857_, v_inst_1858_, v_args_1862_, v_endIdx_1861_, v_f_1859_, v_beginIdx_1860_);
return v___x_1863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRangeS(lean_object* v_m_1864_, lean_object* v_inst_1865_, lean_object* v_inst_1866_, lean_object* v_f_1867_, lean_object* v_beginIdx_1868_, lean_object* v_endIdx_1869_, lean_object* v_args_1870_){
_start:
{
lean_object* v___x_1871_; 
v___x_1871_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg(v_inst_1865_, v_inst_1866_, v_args_1870_, v_endIdx_1869_, v_f_1867_, v_beginIdx_1868_);
return v___x_1871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___redArg(lean_object* v_inst_1872_, lean_object* v_inst_1873_, lean_object* v_f_1874_, lean_object* v_args_1875_){
_start:
{
lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; 
v___x_1876_ = lean_unsigned_to_nat(0u);
v___x_1877_ = lean_array_get_size(v_args_1875_);
v___x_1878_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg(v_inst_1872_, v_inst_1873_, v_args_1875_, v___x_1877_, v_f_1874_, v___x_1876_);
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS(lean_object* v_m_1879_, lean_object* v_inst_1880_, lean_object* v_inst_1881_, lean_object* v_f_1882_, lean_object* v_args_1883_){
_start:
{
lean_object* v___x_1884_; 
v___x_1884_ = l_Lean_Meta_Sym_Internal_mkAppNS___redArg(v_inst_1880_, v_inst_1881_, v_f_1882_, v_args_1883_);
return v___x_1884_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg___lam__0___boxed(lean_object* v_inst_1885_, lean_object* v_inst_1886_, lean_object* v_revArgs_1887_, lean_object* v_start_1888_, lean_object* v_i_1889_, lean_object* v_____do__lift_1890_){
_start:
{
lean_object* v_res_1891_; 
v_res_1891_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg___lam__0(v_inst_1885_, v_inst_1886_, v_revArgs_1887_, v_start_1888_, v_i_1889_, v_____do__lift_1890_);
lean_dec(v_i_1889_);
return v_res_1891_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg(lean_object* v_inst_1892_, lean_object* v_inst_1893_, lean_object* v_revArgs_1894_, lean_object* v_start_1895_, lean_object* v_b_1896_, lean_object* v_i_1897_){
_start:
{
lean_object* v_toApplicative_1898_; lean_object* v_toBind_1899_; lean_object* v_toPure_1900_; uint8_t v___x_1901_; 
v_toApplicative_1898_ = lean_ctor_get(v_inst_1893_, 0);
v_toBind_1899_ = lean_ctor_get(v_inst_1893_, 1);
lean_inc(v_toBind_1899_);
v_toPure_1900_ = lean_ctor_get(v_toApplicative_1898_, 1);
v___x_1901_ = lean_nat_dec_le(v_i_1897_, v_start_1895_);
if (v___x_1901_ == 0)
{
lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v_i_1904_; lean_object* v___f_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___x_1902_ = l_Lean_instInhabitedExpr;
v___x_1903_ = lean_unsigned_to_nat(1u);
v_i_1904_ = lean_nat_sub(v_i_1897_, v___x_1903_);
lean_inc(v_i_1904_);
lean_inc_ref(v_revArgs_1894_);
lean_inc_ref(v_inst_1893_);
lean_inc_ref(v_inst_1892_);
v___f_1905_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1905_, 0, v_inst_1892_);
lean_closure_set(v___f_1905_, 1, v_inst_1893_);
lean_closure_set(v___f_1905_, 2, v_revArgs_1894_);
lean_closure_set(v___f_1905_, 3, v_start_1895_);
lean_closure_set(v___f_1905_, 4, v_i_1904_);
v___x_1906_ = lean_array_get(v___x_1902_, v_revArgs_1894_, v_i_1904_);
lean_dec(v_i_1904_);
lean_dec_ref(v_revArgs_1894_);
v___x_1907_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1892_, v_inst_1893_, v_b_1896_, v___x_1906_);
v___x_1908_ = lean_apply_4(v_toBind_1899_, lean_box(0), lean_box(0), v___x_1907_, v___f_1905_);
return v___x_1908_;
}
else
{
lean_object* v___x_1909_; 
lean_inc(v_toPure_1900_);
lean_dec(v_toBind_1899_);
lean_dec(v_start_1895_);
lean_dec_ref(v_revArgs_1894_);
lean_dec_ref(v_inst_1893_);
lean_dec_ref(v_inst_1892_);
v___x_1909_ = lean_apply_2(v_toPure_1900_, lean_box(0), v_b_1896_);
return v___x_1909_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg___lam__0(lean_object* v_inst_1910_, lean_object* v_inst_1911_, lean_object* v_revArgs_1912_, lean_object* v_start_1913_, lean_object* v_i_1914_, lean_object* v_____do__lift_1915_){
_start:
{
lean_object* v___x_1916_; 
v___x_1916_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg(v_inst_1910_, v_inst_1911_, v_revArgs_1912_, v_start_1913_, v_____do__lift_1915_, v_i_1914_);
return v___x_1916_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg___boxed(lean_object* v_inst_1917_, lean_object* v_inst_1918_, lean_object* v_revArgs_1919_, lean_object* v_start_1920_, lean_object* v_b_1921_, lean_object* v_i_1922_){
_start:
{
lean_object* v_res_1923_; 
v_res_1923_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg(v_inst_1917_, v_inst_1918_, v_revArgs_1919_, v_start_1920_, v_b_1921_, v_i_1922_);
lean_dec(v_i_1922_);
return v_res_1923_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go(lean_object* v_m_1924_, lean_object* v_inst_1925_, lean_object* v_inst_1926_, lean_object* v_revArgs_1927_, lean_object* v_start_1928_, lean_object* v_b_1929_, lean_object* v_i_1930_){
_start:
{
lean_object* v___x_1931_; 
v___x_1931_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg(v_inst_1925_, v_inst_1926_, v_revArgs_1927_, v_start_1928_, v_b_1929_, v_i_1930_);
return v___x_1931_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___boxed(lean_object* v_m_1932_, lean_object* v_inst_1933_, lean_object* v_inst_1934_, lean_object* v_revArgs_1935_, lean_object* v_start_1936_, lean_object* v_b_1937_, lean_object* v_i_1938_){
_start:
{
lean_object* v_res_1939_; 
v_res_1939_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go(v_m_1932_, v_inst_1933_, v_inst_1934_, v_revArgs_1935_, v_start_1936_, v_b_1937_, v_i_1938_);
lean_dec(v_i_1938_);
return v_res_1939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevRangeS___redArg(lean_object* v_inst_1940_, lean_object* v_inst_1941_, lean_object* v_f_1942_, lean_object* v_beginIdx_1943_, lean_object* v_endIdx_1944_, lean_object* v_revArgs_1945_){
_start:
{
lean_object* v___x_1946_; 
v___x_1946_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg(v_inst_1940_, v_inst_1941_, v_revArgs_1945_, v_beginIdx_1943_, v_f_1942_, v_endIdx_1944_);
return v___x_1946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevRangeS___redArg___boxed(lean_object* v_inst_1947_, lean_object* v_inst_1948_, lean_object* v_f_1949_, lean_object* v_beginIdx_1950_, lean_object* v_endIdx_1951_, lean_object* v_revArgs_1952_){
_start:
{
lean_object* v_res_1953_; 
v_res_1953_ = l_Lean_Meta_Sym_Internal_mkAppRevRangeS___redArg(v_inst_1947_, v_inst_1948_, v_f_1949_, v_beginIdx_1950_, v_endIdx_1951_, v_revArgs_1952_);
lean_dec(v_endIdx_1951_);
return v_res_1953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevRangeS(lean_object* v_m_1954_, lean_object* v_inst_1955_, lean_object* v_inst_1956_, lean_object* v_f_1957_, lean_object* v_beginIdx_1958_, lean_object* v_endIdx_1959_, lean_object* v_revArgs_1960_){
_start:
{
lean_object* v___x_1961_; 
v___x_1961_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg(v_inst_1955_, v_inst_1956_, v_revArgs_1960_, v_beginIdx_1958_, v_f_1957_, v_endIdx_1959_);
return v___x_1961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevRangeS___boxed(lean_object* v_m_1962_, lean_object* v_inst_1963_, lean_object* v_inst_1964_, lean_object* v_f_1965_, lean_object* v_beginIdx_1966_, lean_object* v_endIdx_1967_, lean_object* v_revArgs_1968_){
_start:
{
lean_object* v_res_1969_; 
v_res_1969_ = l_Lean_Meta_Sym_Internal_mkAppRevRangeS(v_m_1962_, v_inst_1963_, v_inst_1964_, v_f_1965_, v_beginIdx_1966_, v_endIdx_1967_, v_revArgs_1968_);
lean_dec(v_endIdx_1967_);
return v_res_1969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevS___redArg(lean_object* v_inst_1970_, lean_object* v_inst_1971_, lean_object* v_f_1972_, lean_object* v_revArgs_1973_){
_start:
{
lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; 
v___x_1974_ = lean_unsigned_to_nat(0u);
v___x_1975_ = lean_array_get_size(v_revArgs_1973_);
v___x_1976_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg(v_inst_1970_, v_inst_1971_, v_revArgs_1973_, v___x_1974_, v_f_1972_, v___x_1975_);
return v___x_1976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevS(lean_object* v_m_1977_, lean_object* v_inst_1978_, lean_object* v_inst_1979_, lean_object* v_f_1980_, lean_object* v_revArgs_1981_){
_start:
{
lean_object* v___x_1982_; 
v___x_1982_ = l_Lean_Meta_Sym_Internal_mkAppRevS___redArg(v_inst_1978_, v_inst_1979_, v_f_1980_, v_revArgs_1981_);
return v___x_1982_;
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
